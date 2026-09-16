package machine

import (
	"fmt"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// The RV64 OptIR selector allocates only caller-saved integer registers.
// x31/t6 is deliberately absent: it breaks parallel-copy cycles and provides
// the temporary low half when a constant needs more than one `li`.
var optIRRV64Registers = []int{5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30}

const optIRRV64CopyScratch = 31

// LowerOptIRRV64 selects an admitted RV64 body from a verified optimized
// OptIR CFG. Its vocabulary is deliberately closed: Bool and fixed-width
// integer constants, copies, widening casts, total arithmetic, comparisons,
// branches, and SSA edge arguments. Effects, trapping operations, calls,
// memory, stack arguments, and excess register pressure refuse the candidate.
//
// RV64's 32-bit instructions sign-extend their result to XLEN. Oak therefore
// keeps both i32 and u32 in that canonical W-value representation; only a
// later widening of u32 to u64 explicitly clears the high half. The native
// candidate search must still seam-check and translation-validate the body
// before it may ship.
func LowerOptIRRV64(cfg optir.CFG, template *asm.Function) (*asm.Function, error) {
	if template == nil || template.Signature == nil || template.Signature.Name == nil {
		return nil, fmt.Errorf("machine: OptIR lowering needs an assembler function template")
	}
	if template.Arch != "" && template.Arch != asm.ArchRV64 {
		return nil, fmt.Errorf("machine: OptIR RV64 selector received %s template", template.Arch)
	}
	if err := optir.Verify(cfg); err != nil {
		return nil, fmt.Errorf("machine: OptIR selector input: %w", err)
	}
	if cfg.Name != template.Signature.Name.Value {
		return nil, fmt.Errorf("machine: OptIR function %s does not match template %s", cfg.Name, template.Signature.Name.Value)
	}
	if len(cfg.Results) != 1 {
		return nil, fmt.Errorf("machine: OptIR selector supports one result, got %d", len(cfg.Results))
	}
	types := optIRTypes(cfg)
	for value, typ := range types {
		if _, _, ok := optIRRV64Type(typ); !ok && typ != optir.TypeBool && typ != optir.Type("()") {
			return nil, fmt.Errorf("machine: OptIR value %d has unsupported RV64 type %s", value, typ)
		}
	}
	entry := optIRBlock(cfg, cfg.Entry)
	if entry == nil {
		return nil, fmt.Errorf("machine: OptIR entry block %d is missing", cfg.Entry)
	}
	for _, block := range cfg.Blocks {
		for _, edge := range optIRTerminatorEdges(block.Terminator) {
			if edge.Target == cfg.Entry {
				return nil, fmt.Errorf("machine: OptIR selector refuses an edge back to entry block %d", cfg.Entry)
			}
		}
	}
	fixed, err := optIRRV64ParameterColors(entry.Parameters, template.Bindings)
	if err != nil {
		return nil, err
	}
	coloring, err := optir.ColorRegisters(cfg, optIRRV64Registers, fixed)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR RV64 allocation: %w", err)
	}

	selector := &optIRRV64Selector{
		cfg: cfg, types: types, colors: coloring.Colors,
		labels: map[optir.BlockID]string{}, written: map[int]bool{},
	}
	for _, block := range cfg.Blocks {
		selector.labels[block.ID] = "optir_b" + strconv.FormatUint(uint64(block.ID), 10)
	}
	if err := selector.lower(); err != nil {
		return nil, err
	}

	out := *template
	out.Arch = asm.ArchRV64
	out.Items = selector.items
	out.Bindings = append([]asm.Binding(nil), template.Bindings...)
	out.Clobbers = nil
	out.Frame = 0
	out.System = false
	out.Globals = nil
	out.StackArgs = 0
	out.Body = nil
	bound := map[int]bool{}
	for _, binding := range out.Bindings {
		if !binding.OnStack {
			bound[binding.Register.Num] = true
		}
	}
	var clobbers []int
	for register := range selector.written {
		resultRegister := register == 10 && cfg.Results[0] != optir.Type("()")
		if !bound[register] && !resultRegister {
			clobbers = append(clobbers, register)
		}
	}
	sort.Ints(clobbers)
	for _, register := range clobbers {
		out.Clobbers = append(out.Clobbers, optIRRV64Register(register))
	}
	return &out, nil
}

type optIRRV64Selector struct {
	cfg     optir.CFG
	types   map[optir.ValueID]optir.Type
	colors  map[optir.ValueID]int
	labels  map[optir.BlockID]string
	items   []asm.Item
	written map[int]bool
	edges   int
}

func (selector *optIRRV64Selector) lower() error {
	for _, block := range selector.cfg.Blocks {
		line := optIRBlockLine(block)
		selector.items = append(selector.items, asm.Label{Name: selector.labels[block.ID], Line: line})
		if block.ID == selector.cfg.Entry {
			// Do not let unspecified ABI padding become part of an Oak value.
			// Bool retains one bit; narrow integers are restored to their
			// signed or unsigned canonical representation before first use.
			for _, parameter := range block.Parameters {
				selector.normalize(selector.register(parameter.ID), parameter.Type, line)
			}
		}
		for _, operation := range block.Operations {
			if err := selector.operation(operation); err != nil {
				return fmt.Errorf("machine: OptIR block %d operation %s: %w", block.ID, operation.Code, err)
			}
		}
		if err := selector.terminator(block, line); err != nil {
			return fmt.Errorf("machine: OptIR block %d terminator: %w", block.ID, err)
		}
	}
	return nil
}

func (selector *optIRRV64Selector) operation(operation optir.Operation) error {
	if len(operation.Effects) != 0 {
		return fmt.Errorf("effectful operation %s", operation.Code)
	}
	if len(operation.Results) != 1 {
		return fmt.Errorf("operation has %d results, want one", len(operation.Results))
	}
	result := operation.Results[0]
	line := operation.Source.Line
	if line <= 0 {
		line = result.Source.Line
	}
	destination := selector.register(result.ID)
	switch operation.Code {
	case optir.OpConstUnit:
		if result.Type != optir.Type("()") || len(operation.Operands) != 0 || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed unit constant")
		}
		return nil
	case optir.OpConstBool:
		if result.Type != optir.TypeBool || len(operation.Operands) != 0 {
			return fmt.Errorf("malformed Bool constant")
		}
		value, ok := optIRAttribute(operation, optir.AttributeValue)
		if !ok || value != "true" && value != "false" {
			return fmt.Errorf("invalid Bool constant %q", value)
		}
		bits := uint64(0)
		if value == "true" {
			bits = 1
		}
		selector.constant(destination, int64(bits), line)
		return nil
	case optir.OpConstInt:
		_, _, ok := optIRRV64Type(result.Type)
		if !ok || len(operation.Operands) != 0 {
			return fmt.Errorf("malformed integer constant of type %s", result.Type)
		}
		spelling, ok := optIRAttribute(operation, optir.AttributeValue)
		if !ok {
			return fmt.Errorf("integer constant has no value")
		}
		value, err := optIRIntegerConstant(spelling, result.Type)
		if err != nil {
			return fmt.Errorf("invalid %s constant %q", result.Type, spelling)
		}
		selector.constant(destination, optIRRV64Canonical(value, result.Type), line)
		return nil
	case optir.OpCopy:
		if len(operation.Operands) != 1 || selector.types[operation.Operands[0]] != result.Type || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed copy")
		}
		if result.Type != optir.Type("()") {
			selector.move(destination, selector.register(operation.Operands[0]), line)
		}
		return nil
	case optir.OpCastInt:
		if len(operation.Operands) != 1 || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed integer cast")
		}
		return selector.cast(destination, result.Type, operation.Operands[0], line)
	case optir.OpBoolNot:
		if len(operation.Operands) != 1 || result.Type != optir.TypeBool || selector.types[operation.Operands[0]] != optir.TypeBool || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed Bool negation")
		}
		selector.emit("xori", line, optIRRV64Register(destination), optIRRV64Register(selector.register(operation.Operands[0])), asm.Immediate{Value: 1})
		return nil
	case optir.OpIntNeg:
		if err := selector.sameIntegerOperation(operation, 1); err != nil {
			return err
		}
		mnemonic := "neg"
		if optIRRV64Bits(result.Type) == 32 {
			mnemonic = "negw"
		}
		selector.emit(mnemonic, line, optIRRV64Register(destination), optIRRV64Register(selector.register(operation.Operands[0])))
		selector.normalize(destination, result.Type, line)
		return nil
	case optir.OpIntAdd, optir.OpIntSub, optir.OpIntMul, optir.OpIntAnd, optir.OpIntOr, optir.OpIntXor:
		if err := selector.sameIntegerOperation(operation, 2); err != nil {
			return err
		}
		mnemonic := map[string]string{
			optir.OpIntAdd: "add", optir.OpIntSub: "sub", optir.OpIntMul: "mul",
			optir.OpIntAnd: "and", optir.OpIntOr: "or", optir.OpIntXor: "xor",
		}[operation.Code]
		bits, _, _ := optIRRV64Type(result.Type)
		if bits == 32 && (operation.Code == optir.OpIntAdd || operation.Code == optir.OpIntSub || operation.Code == optir.OpIntMul) {
			mnemonic += "w"
		}
		selector.emit(mnemonic, line, optIRRV64Register(destination), optIRRV64Register(selector.register(operation.Operands[0])), optIRRV64Register(selector.register(operation.Operands[1])))
		selector.normalize(destination, result.Type, line)
		return nil
	case optir.OpEqual, optir.OpNotEqual, optir.OpLess, optir.OpLessEqual, optir.OpGreater, optir.OpGreaterEqual:
		return selector.compare(operation, line)
	default:
		return fmt.Errorf("operation %s is outside the closed selector vocabulary", operation.Code)
	}
}

func (selector *optIRRV64Selector) sameIntegerOperation(operation optir.Operation, arity int) error {
	if len(operation.Operands) != arity || len(operation.Attributes) != 0 {
		return fmt.Errorf("malformed %s", operation.Code)
	}
	result := operation.Results[0]
	if _, _, ok := optIRRV64Type(result.Type); !ok {
		return fmt.Errorf("%s result has non-integer type %s", operation.Code, result.Type)
	}
	for _, operand := range operation.Operands {
		if selector.types[operand] != result.Type {
			return fmt.Errorf("%s mixes %s and %s", operation.Code, result.Type, selector.types[operand])
		}
	}
	return nil
}

func (selector *optIRRV64Selector) cast(destination int, resultType optir.Type, operand optir.ValueID, line int) error {
	fromType := selector.types[operand]
	if !optIRRV64ValidWidening(fromType, resultType) {
		return fmt.Errorf("unsupported value-preserving cast %s to %s", fromType, resultType)
	}
	toBits, _, _ := optIRRV64Type(resultType)
	fromBits, fromSigned, _ := optIRRV64Type(fromType)
	source := selector.register(operand)
	selector.move(destination, source, line)
	if fromBits == 32 && toBits == 64 && !fromSigned {
		// W values are sign-extended on RV64, including Oak u32. This is
		// the one value-preserving widening that must clear the high half.
		selector.emit("slli", line, optIRRV64Register(destination), optIRRV64Register(destination), asm.Immediate{Value: 32})
		selector.emit("srli", line, optIRRV64Register(destination), optIRRV64Register(destination), asm.Immediate{Value: 32})
		return nil
	}
	selector.normalize(destination, resultType, line)
	return nil
}

func (selector *optIRRV64Selector) compare(operation optir.Operation, line int) error {
	if len(operation.Operands) != 2 || len(operation.Attributes) != 0 || operation.Results[0].Type != optir.TypeBool {
		return fmt.Errorf("malformed comparison")
	}
	leftType, rightType := selector.types[operation.Operands[0]], selector.types[operation.Operands[1]]
	if leftType != rightType {
		return fmt.Errorf("comparison mixes %s and %s", leftType, rightType)
	}
	_, signed, integer := optIRRV64Type(leftType)
	if !integer && leftType != optir.TypeBool {
		return fmt.Errorf("comparison operand has unsupported type %s", leftType)
	}
	if (operation.Code == optir.OpLess || operation.Code == optir.OpLessEqual || operation.Code == optir.OpGreater || operation.Code == optir.OpGreaterEqual) && !integer {
		return fmt.Errorf("ordered comparison of %s", leftType)
	}
	destination := optIRRV64Register(selector.register(operation.Results[0].ID))
	left := optIRRV64Register(selector.register(operation.Operands[0]))
	right := optIRRV64Register(selector.register(operation.Operands[1]))
	switch operation.Code {
	case optir.OpEqual, optir.OpNotEqual:
		selector.emit("sub", line, destination, left, right)
		mnemonic := "seqz"
		if operation.Code == optir.OpNotEqual {
			mnemonic = "snez"
		}
		selector.emit(mnemonic, line, destination, destination)
	case optir.OpLess, optir.OpGreater:
		mnemonic := "sltu"
		if signed {
			mnemonic = "slt"
		}
		if operation.Code == optir.OpLess {
			selector.emit(mnemonic, line, destination, left, right)
		} else {
			selector.emit(mnemonic, line, destination, right, left)
		}
	case optir.OpLessEqual, optir.OpGreaterEqual:
		mnemonic := "sltu"
		if signed {
			mnemonic = "slt"
		}
		if operation.Code == optir.OpLessEqual {
			selector.emit(mnemonic, line, destination, right, left)
		} else {
			selector.emit(mnemonic, line, destination, left, right)
		}
		selector.emit("xori", line, destination, destination, asm.Immediate{Value: 1})
	}
	return nil
}

func (selector *optIRRV64Selector) terminator(block optir.Block, line int) error {
	switch terminator := block.Terminator; terminator.Kind {
	case optir.TerminatorReturn:
		if len(terminator.Values) != 1 {
			return fmt.Errorf("return has %d values", len(terminator.Values))
		}
		value := terminator.Values[0]
		if selector.types[value] != optir.Type("()") {
			selector.move(10, selector.register(value), line)
		}
		selector.emit("ret", line)
		return nil
	case optir.TerminatorBranch:
		if err := selector.edgeCopies(terminator.True, line); err != nil {
			return err
		}
		selector.emit("j", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		return nil
	case optir.TerminatorCondBranch:
		if selector.types[terminator.Condition] != optir.TypeBool {
			return fmt.Errorf("condition %d is not Bool", terminator.Condition)
		}
		trueLabel := selector.edgeLabel(block.ID, "true")
		falseLabel := selector.edgeLabel(block.ID, "false")
		selector.emit("bnez", line, optIRRV64Register(selector.register(terminator.Condition)), asm.Symbol{Name: trueLabel})
		selector.emit("j", line, asm.Symbol{Name: falseLabel})
		selector.items = append(selector.items, asm.Label{Name: trueLabel, Line: line})
		if err := selector.edgeCopies(terminator.True, line); err != nil {
			return err
		}
		selector.emit("j", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		selector.items = append(selector.items, asm.Label{Name: falseLabel, Line: line})
		if err := selector.edgeCopies(terminator.False, line); err != nil {
			return err
		}
		selector.emit("j", line, asm.Symbol{Name: selector.labels[terminator.False.Target]})
		return nil
	default:
		return fmt.Errorf("unsupported terminator %s", terminator.Kind)
	}
}

type optIRRV64Move struct {
	destination int
	source      int
}

func (selector *optIRRV64Selector) edgeCopies(edge optir.Edge, line int) error {
	target := optIRBlock(selector.cfg, edge.Target)
	if target == nil || len(target.Parameters) != len(edge.Arguments) {
		return fmt.Errorf("invalid edge to block %d", edge.Target)
	}
	var moves []optIRRV64Move
	for index, parameter := range target.Parameters {
		argument := edge.Arguments[index]
		if parameter.Type == optir.Type("()") {
			continue
		}
		if selector.types[argument] != parameter.Type {
			return fmt.Errorf("edge to block %d passes %s to %s parameter %s", edge.Target, selector.types[argument], parameter.Type, parameter.Name)
		}
		destination, source := selector.register(parameter.ID), selector.register(argument)
		if destination != source {
			moves = append(moves, optIRRV64Move{destination: destination, source: source})
		}
	}
	for len(moves) > 0 {
		progress := false
		for index, move := range moves {
			usedAsSource := false
			for _, other := range moves {
				usedAsSource = usedAsSource || other.source == move.destination
			}
			if usedAsSource {
				continue
			}
			selector.move(move.destination, move.source, line)
			moves = append(moves[:index], moves[index+1:]...)
			progress = true
			break
		}
		if progress {
			continue
		}
		cycle := moves[0].destination
		selector.move(optIRRV64CopyScratch, cycle, line)
		for index := range moves {
			if moves[index].source == cycle {
				moves[index].source = optIRRV64CopyScratch
			}
		}
	}
	return nil
}

func (selector *optIRRV64Selector) constant(destination int, value int64, line int) {
	dst := optIRRV64Register(destination)
	if value >= -(1<<31) && value < 1<<31 {
		selector.emit("li", line, dst, asm.Immediate{Value: value})
		return
	}
	lo := int64(int32(uint32(uint64(value))))
	hi := int64(int32(uint32((uint64(value) - uint64(lo)) >> 32)))
	selector.emit("li", line, dst, asm.Immediate{Value: hi})
	selector.emit("slli", line, dst, dst, asm.Immediate{Value: 32})
	scratch := optIRRV64Register(optIRRV64CopyScratch)
	selector.emit("li", line, scratch, asm.Immediate{Value: lo})
	selector.emit("add", line, dst, dst, scratch)
}

func (selector *optIRRV64Selector) move(destination, source, line int) {
	if destination == source {
		return
	}
	selector.emit("mv", line, optIRRV64Register(destination), optIRRV64Register(source))
}

func (selector *optIRRV64Selector) normalize(register int, typ optir.Type, line int) {
	if typ == optir.TypeBool {
		r := optIRRV64Register(register)
		selector.emit("andi", line, r, r, asm.Immediate{Value: 1})
		return
	}
	bits, signed, ok := optIRRV64Type(typ)
	if !ok || bits >= 32 {
		return
	}
	r := optIRRV64Register(register)
	switch {
	case bits == 8 && signed:
		selector.emit("slli", line, r, r, asm.Immediate{Value: 56})
		selector.emit("srai", line, r, r, asm.Immediate{Value: 56})
	case bits == 8:
		selector.emit("andi", line, r, r, asm.Immediate{Value: 255})
	case signed:
		selector.emit("slli", line, r, r, asm.Immediate{Value: 48})
		selector.emit("srai", line, r, r, asm.Immediate{Value: 48})
	default:
		selector.emit("slli", line, r, r, asm.Immediate{Value: 48})
		selector.emit("srli", line, r, r, asm.Immediate{Value: 48})
	}
}

func (selector *optIRRV64Selector) emit(mnemonic string, line int, operands ...asm.Operand) {
	selector.items = append(selector.items, asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: line})
	if len(operands) == 0 {
		return
	}
	destination, ok := operands[0].(asm.Register)
	if !ok {
		return
	}
	switch mnemonic {
	case "li", "mv", "xori", "neg", "negw", "add", "addw", "sub", "subw", "mul", "mulw", "and", "andi", "or", "xor", "slli", "srli", "srai", "slt", "sltu", "seqz", "snez":
		if destination.Num != 0 {
			selector.written[destination.Num] = true
		}
	}
}

func (selector *optIRRV64Selector) register(value optir.ValueID) int {
	return selector.colors[value]
}

func (selector *optIRRV64Selector) edgeLabel(block optir.BlockID, side string) string {
	selector.edges++
	return "optir_e" + strconv.FormatUint(uint64(block), 10) + "_" + side + "_" + strconv.Itoa(selector.edges)
}

func optIRRV64ParameterColors(parameters []optir.Value, bindings []asm.Binding) (map[optir.ValueID]int, error) {
	byName := map[string]asm.Binding{}
	for _, binding := range bindings {
		if binding.OnStack || binding.Length != nil || binding.Register.Class != asm.ClassRV64X {
			return nil, fmt.Errorf("machine: OptIR RV64 selector refuses non-scalar or stack parameter %s", binding.Param)
		}
		byName[binding.Param] = binding
	}
	if len(byName) != len(parameters) {
		return nil, fmt.Errorf("machine: OptIR entry has %d parameters, template binds %d", len(parameters), len(byName))
	}
	out := map[optir.ValueID]int{}
	for _, parameter := range parameters {
		if parameter.Type == optir.Type("()") {
			return nil, fmt.Errorf("machine: OptIR RV64 selector refuses unit parameter %s", parameter.Name)
		}
		if parameter.Type != optir.TypeBool {
			if _, _, ok := optIRRV64Type(parameter.Type); !ok {
				return nil, fmt.Errorf("machine: OptIR parameter %s has unsupported RV64 type %s", parameter.Name, parameter.Type)
			}
		}
		binding, exists := byName[parameter.Name]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR parameter %s has no ABI binding", parameter.Name)
		}
		out[parameter.ID] = binding.Register.Num
	}
	return out, nil
}

func optIRRV64Type(typ optir.Type) (bits int, signed, ok bool) {
	switch typ {
	case "u8":
		return 8, false, true
	case "i8":
		return 8, true, true
	case "u16":
		return 16, false, true
	case "i16":
		return 16, true, true
	case "u32":
		return 32, false, true
	case "i32":
		return 32, true, true
	case "u64":
		return 64, false, true
	case "i64":
		return 64, true, true
	}
	return 0, false, false
}

func optIRRV64Bits(typ optir.Type) int {
	bits, _, _ := optIRRV64Type(typ)
	return bits
}

func optIRRV64ValidWidening(source, target optir.Type) bool {
	sourceBits, sourceSigned, sourceOK := optIRRV64Type(source)
	targetBits, targetSigned, targetOK := optIRRV64Type(target)
	if !sourceOK || !targetOK {
		return false
	}
	if sourceSigned == targetSigned {
		return sourceBits <= targetBits
	}
	return !sourceSigned && targetSigned && sourceBits < targetBits
}

func optIRRV64Canonical(value uint64, typ optir.Type) int64 {
	bits, signed, _ := optIRRV64Type(typ)
	switch {
	case bits == 64:
		return int64(value)
	case bits == 32:
		return int64(int32(uint32(value)))
	case bits == 16 && signed:
		return int64(int16(uint16(value)))
	case bits == 16:
		return int64(uint16(value))
	case signed:
		return int64(int8(uint8(value)))
	default:
		return int64(uint8(value))
	}
}

func optIRRV64Register(register int) asm.Register {
	return asm.Register{Text: rv64Names[register], Class: asm.ClassRV64X, Num: register, Lane: -1}
}
