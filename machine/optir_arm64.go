package machine

import (
	"fmt"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/optir"
)

// The OptIR selector uses only caller-saved general registers. x8 is the
// indirect-result register, x17 is reserved for parallel-copy cycles, and x18
// is platform-reserved. Calls and memory effects are outside this first seam.
var optIRArm64Registers = []int{0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16}

const optIRCopyScratch = 17

// LowerOptIRArm64 selects an admitted AArch64 body from a verified optimized
// OptIR CFG. It deliberately supports a small closed vocabulary: Bool and
// 32/64-bit integer constants, copies, widening casts, total arithmetic,
// comparisons, branches, and SSA edge arguments. Effects, trapping operations,
// calls, narrow-integer normalization, stack arguments, and excess register
// pressure refuse the candidate. The native search independently seam-checks
// and translation-validates every returned body before it may ship.
func LowerOptIRArm64(cfg optir.CFG, template *asm.Function) (*asm.Function, error) {
	if template == nil || template.Signature == nil || template.Signature.Name == nil {
		return nil, fmt.Errorf("machine: OptIR lowering needs an assembler function template")
	}
	if template.Arch != "" && template.Arch != asm.ArchArm64 {
		return nil, fmt.Errorf("machine: OptIR AArch64 selector received %s template", template.Arch)
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
		if _, _, ok := optIRArm64Type(typ); !ok && typ != optir.TypeBool && typ != optir.Type("()") {
			return nil, fmt.Errorf("machine: OptIR value %d has unsupported AArch64 type %s", value, typ)
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
	fixed, err := optIRParameterColors(entry.Parameters, template.Bindings)
	if err != nil {
		return nil, err
	}
	coloring, err := optir.ColorRegisters(cfg, optIRArm64Registers, fixed)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR AArch64 allocation: %w", err)
	}

	selector := &optIRArm64Selector{
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
	out.Arch = asm.ArchArm64
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
		if !bound[register] && register != 0 {
			clobbers = append(clobbers, register)
		}
	}
	sort.Ints(clobbers)
	for _, register := range clobbers {
		out.Clobbers = append(out.Clobbers, arm64X(register))
	}
	return &out, nil
}

type optIRArm64Selector struct {
	cfg     optir.CFG
	types   map[optir.ValueID]optir.Type
	colors  map[optir.ValueID]int
	labels  map[optir.BlockID]string
	items   []asm.Item
	written map[int]bool
	edges   int
}

func (selector *optIRArm64Selector) lower() error {
	for _, block := range selector.cfg.Blocks {
		line := optIRBlockLine(block)
		selector.items = append(selector.items, asm.Label{Name: selector.labels[block.ID], Line: line})
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

func (selector *optIRArm64Selector) operation(operation optir.Operation) error {
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
		selector.constant(destination, bits, 32, line)
		return nil
	case optir.OpConstInt:
		bits, _, ok := optIRArm64Type(result.Type)
		if !ok || len(operation.Operands) != 0 {
			return fmt.Errorf("malformed integer constant of type %s", result.Type)
		}
		spelling, ok := optIRAttribute(operation, optir.AttributeValue)
		if !ok {
			return fmt.Errorf("integer constant has no value")
		}
		value, err := strconv.ParseUint(spelling, 10, bits)
		if err != nil {
			return fmt.Errorf("invalid %s constant %q", result.Type, spelling)
		}
		selector.constant(destination, value, bits, line)
		return nil
	case optir.OpCopy:
		if len(operation.Operands) != 1 || selector.types[operation.Operands[0]] != result.Type || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed copy")
		}
		selector.move(destination, selector.register(operation.Operands[0]), optIRBits(result.Type), line)
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
		selector.emit("eor", line, optIRW(destination), optIRW(selector.register(operation.Operands[0])), asm.Immediate{Value: 1})
		return nil
	case optir.OpIntNeg:
		if err := selector.sameIntegerOperation(operation, 1); err != nil {
			return err
		}
		selector.emit("neg", line, selector.valueRegister(result.ID), selector.valueRegister(operation.Operands[0]))
		return nil
	case optir.OpIntAdd, optir.OpIntSub, optir.OpIntMul, optir.OpIntAnd, optir.OpIntOr, optir.OpIntXor:
		if err := selector.sameIntegerOperation(operation, 2); err != nil {
			return err
		}
		mnemonic := map[string]string{
			optir.OpIntAdd: "add", optir.OpIntSub: "sub", optir.OpIntMul: "mul",
			optir.OpIntAnd: "and", optir.OpIntOr: "orr", optir.OpIntXor: "eor",
		}[operation.Code]
		selector.emit(mnemonic, line, selector.valueRegister(result.ID), selector.valueRegister(operation.Operands[0]), selector.valueRegister(operation.Operands[1]))
		return nil
	case optir.OpEqual, optir.OpNotEqual, optir.OpLess, optir.OpLessEqual, optir.OpGreater, optir.OpGreaterEqual:
		return selector.compare(operation, line)
	default:
		return fmt.Errorf("operation %s is outside the closed selector vocabulary", operation.Code)
	}
}

func (selector *optIRArm64Selector) sameIntegerOperation(operation optir.Operation, arity int) error {
	if len(operation.Operands) != arity || len(operation.Attributes) != 0 {
		return fmt.Errorf("malformed %s", operation.Code)
	}
	result := operation.Results[0]
	if _, _, ok := optIRArm64Type(result.Type); !ok {
		return fmt.Errorf("%s result has non-integer type %s", operation.Code, result.Type)
	}
	for _, operand := range operation.Operands {
		if selector.types[operand] != result.Type {
			return fmt.Errorf("%s mixes %s and %s", operation.Code, result.Type, selector.types[operand])
		}
	}
	return nil
}

func (selector *optIRArm64Selector) cast(destination int, resultType optir.Type, operand optir.ValueID, line int) error {
	toBits, _, toOK := optIRArm64Type(resultType)
	fromType := selector.types[operand]
	fromBits, fromSigned, fromOK := optIRArm64Type(fromType)
	if !toOK || !fromOK || fromBits > toBits {
		return fmt.Errorf("unsupported value-preserving cast %s to %s", fromType, resultType)
	}
	source := selector.register(operand)
	switch {
	case fromBits == toBits:
		selector.move(destination, source, toBits, line)
	case fromBits == 32 && toBits == 64 && fromSigned:
		selector.emit("sxtw", line, arm64X(destination), optIRW(source))
	case fromBits == 32 && toBits == 64:
		// A W write zeroes the upper half of its X register.
		selector.move(destination, source, 32, line)
	default:
		return fmt.Errorf("unsupported value-preserving cast %s to %s", fromType, resultType)
	}
	return nil
}

func (selector *optIRArm64Selector) compare(operation optir.Operation, line int) error {
	if len(operation.Operands) != 2 || len(operation.Attributes) != 0 || operation.Results[0].Type != optir.TypeBool {
		return fmt.Errorf("malformed comparison")
	}
	leftType, rightType := selector.types[operation.Operands[0]], selector.types[operation.Operands[1]]
	if leftType != rightType {
		return fmt.Errorf("comparison mixes %s and %s", leftType, rightType)
	}
	bits, signed, integer := optIRArm64Type(leftType)
	if !integer && leftType != optir.TypeBool {
		return fmt.Errorf("comparison operand has unsupported type %s", leftType)
	}
	if leftType == optir.TypeBool {
		bits = 32
	}
	if (operation.Code == optir.OpLess || operation.Code == optir.OpLessEqual || operation.Code == optir.OpGreater || operation.Code == optir.OpGreaterEqual) && !integer {
		return fmt.Errorf("ordered comparison of %s", leftType)
	}
	condition := map[string]string{optir.OpEqual: "eq", optir.OpNotEqual: "ne"}[operation.Code]
	if condition == "" {
		if signed {
			condition = map[string]string{optir.OpLess: "lt", optir.OpLessEqual: "le", optir.OpGreater: "gt", optir.OpGreaterEqual: "ge"}[operation.Code]
		} else {
			condition = map[string]string{optir.OpLess: "lo", optir.OpLessEqual: "ls", optir.OpGreater: "hi", optir.OpGreaterEqual: "hs"}[operation.Code]
		}
	}
	selector.emit("cmp", line, optIRRegister(selector.register(operation.Operands[0]), bits), optIRRegister(selector.register(operation.Operands[1]), bits))
	selector.emit("cset", line, optIRW(selector.register(operation.Results[0].ID)), asm.Condition{Code: condition})
	return nil
}

func (selector *optIRArm64Selector) terminator(block optir.Block, line int) error {
	switch terminator := block.Terminator; terminator.Kind {
	case optir.TerminatorReturn:
		if len(terminator.Values) != 1 {
			return fmt.Errorf("return has %d values", len(terminator.Values))
		}
		value := terminator.Values[0]
		if selector.types[value] != optir.Type("()") {
			selector.move(0, selector.register(value), optIRBits(selector.types[value]), line)
		}
		selector.emit("ret", line)
		return nil
	case optir.TerminatorBranch:
		if err := selector.edgeCopies(terminator.True, line); err != nil {
			return err
		}
		selector.emit("b", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		return nil
	case optir.TerminatorCondBranch:
		if selector.types[terminator.Condition] != optir.TypeBool {
			return fmt.Errorf("condition %d is not Bool", terminator.Condition)
		}
		trueLabel := selector.edgeLabel(block.ID, "true")
		falseLabel := selector.edgeLabel(block.ID, "false")
		selector.emit("cbnz", line, optIRW(selector.register(terminator.Condition)), asm.Symbol{Name: trueLabel})
		selector.emit("b", line, asm.Symbol{Name: falseLabel})
		selector.items = append(selector.items, asm.Label{Name: trueLabel, Line: line})
		if err := selector.edgeCopies(terminator.True, line); err != nil {
			return err
		}
		selector.emit("b", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		selector.items = append(selector.items, asm.Label{Name: falseLabel, Line: line})
		if err := selector.edgeCopies(terminator.False, line); err != nil {
			return err
		}
		selector.emit("b", line, asm.Symbol{Name: selector.labels[terminator.False.Target]})
		return nil
	default:
		return fmt.Errorf("unsupported terminator %s", terminator.Kind)
	}
}

type optIRRegisterMove struct{ destination, source int }

func (selector *optIRArm64Selector) edgeCopies(edge optir.Edge, line int) error {
	target := optIRBlock(selector.cfg, edge.Target)
	if target == nil || len(target.Parameters) != len(edge.Arguments) {
		return fmt.Errorf("invalid edge to block %d", edge.Target)
	}
	var moves []optIRRegisterMove
	for index, parameter := range target.Parameters {
		argument := edge.Arguments[index]
		if parameter.Type == optir.Type("()") {
			continue
		}
		destination, source := selector.register(parameter.ID), selector.register(argument)
		if destination != source {
			moves = append(moves, optIRRegisterMove{destination: destination, source: source})
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
			selector.move(move.destination, move.source, 64, line)
			moves = append(moves[:index], moves[index+1:]...)
			progress = true
			break
		}
		if progress {
			continue
		}
		// A cycle: save one destination's old value, then replace every
		// use of it with the reserved scratch and continue acyclically.
		cycle := moves[0].destination
		selector.move(optIRCopyScratch, cycle, 64, line)
		for index := range moves {
			if moves[index].source == cycle {
				moves[index].source = optIRCopyScratch
			}
		}
	}
	return nil
}

func (selector *optIRArm64Selector) constant(destination int, value uint64, bits int, line int) {
	register := optIRRegister(destination, bits)
	if bits == 32 {
		value &= 0xffffffff
	}
	if value == 0 {
		selector.emit("mov", line, register, optIRRegister(31, bits))
		return
	}
	first := true
	for shift := 0; shift < bits; shift += 16 {
		piece := (value >> uint(shift)) & 0xffff
		if piece == 0 {
			continue
		}
		mnemonic := "movk"
		if first {
			mnemonic, first = "movz", false
		}
		selector.emit(mnemonic, line, register, asm.Immediate{Value: int64(piece), Shift: int64(shift)})
	}
}

func (selector *optIRArm64Selector) move(destination, source, bits, line int) {
	if destination == source {
		return
	}
	selector.emit("mov", line, optIRRegister(destination, bits), optIRRegister(source, bits))
}

func (selector *optIRArm64Selector) emit(mnemonic string, line int, operands ...asm.Operand) {
	selector.items = append(selector.items, asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: line})
	if len(operands) == 0 {
		return
	}
	if destination, ok := operands[0].(asm.Register); ok {
		switch mnemonic {
		case "mov", "movz", "movk", "sxtw", "eor", "neg", "add", "sub", "mul", "and", "orr", "cset":
			if !destination.ZeroRegister() {
				selector.written[destination.Num] = true
			}
		}
	}
}

func (selector *optIRArm64Selector) register(value optir.ValueID) int { return selector.colors[value] }

func (selector *optIRArm64Selector) valueRegister(value optir.ValueID) asm.Register {
	return optIRRegister(selector.register(value), optIRBits(selector.types[value]))
}

func (selector *optIRArm64Selector) edgeLabel(block optir.BlockID, side string) string {
	selector.edges++
	return "optir_e" + strconv.FormatUint(uint64(block), 10) + "_" + side + "_" + strconv.Itoa(selector.edges)
}

func optIRTypes(cfg optir.CFG) map[optir.ValueID]optir.Type {
	out := map[optir.ValueID]optir.Type{}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			out[parameter.ID] = parameter.Type
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				out[result.ID] = result.Type
			}
		}
	}
	return out
}

func optIRParameterColors(parameters []optir.Value, bindings []asm.Binding) (map[optir.ValueID]int, error) {
	byName := map[string]asm.Binding{}
	for _, binding := range bindings {
		if binding.OnStack || binding.Length != nil || binding.Register.Class != asm.ClassW && binding.Register.Class != asm.ClassX {
			return nil, fmt.Errorf("machine: OptIR selector refuses non-scalar or stack parameter %s", binding.Param)
		}
		byName[binding.Param] = binding
	}
	if len(byName) != len(parameters) {
		return nil, fmt.Errorf("machine: OptIR entry has %d parameters, template binds %d", len(parameters), len(byName))
	}
	out := map[optir.ValueID]int{}
	for _, parameter := range parameters {
		binding, exists := byName[parameter.Name]
		if !exists {
			return nil, fmt.Errorf("machine: OptIR parameter %s has no ABI binding", parameter.Name)
		}
		bits := optIRBits(parameter.Type)
		if bits == 64 && binding.Register.Class != asm.ClassX || bits == 32 && binding.Register.Class != asm.ClassW {
			return nil, fmt.Errorf("machine: OptIR parameter %s type %s disagrees with %s", parameter.Name, parameter.Type, binding.Register.Text)
		}
		out[parameter.ID] = binding.Register.Num
	}
	return out, nil
}

func optIRAttribute(operation optir.Operation, name string) (string, bool) {
	if len(operation.Attributes) != 1 || operation.Attributes[0].Name != name {
		return "", false
	}
	return operation.Attributes[0].Value, true
}

func optIRArm64Type(typ optir.Type) (bits int, signed, ok bool) {
	switch typ {
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

func optIRBits(typ optir.Type) int {
	if typ == optir.TypeBool {
		return 32
	}
	bits, _, _ := optIRArm64Type(typ)
	return bits
}

func optIRRegister(register, bits int) asm.Register {
	if bits == 64 {
		return arm64X(register)
	}
	return optIRW(register)
}

func optIRW(register int) asm.Register {
	name := "w" + strconv.Itoa(register)
	if register == 31 {
		name = "wzr"
	}
	return asm.Register{Text: name, Class: asm.ClassW, Num: register, Lane: -1}
}

func optIRBlock(cfg optir.CFG, id optir.BlockID) *optir.Block {
	for index := range cfg.Blocks {
		if cfg.Blocks[index].ID == id {
			return &cfg.Blocks[index]
		}
	}
	return nil
}

func optIRTerminatorEdges(terminator optir.Terminator) []optir.Edge {
	switch terminator.Kind {
	case optir.TerminatorBranch:
		return []optir.Edge{terminator.True}
	case optir.TerminatorCondBranch:
		return []optir.Edge{terminator.True, terminator.False}
	}
	return nil
}

func optIRBlockLine(block optir.Block) int {
	for _, parameter := range block.Parameters {
		if parameter.Source.Line > 0 {
			return parameter.Source.Line
		}
	}
	for _, operation := range block.Operations {
		if operation.Source.Line > 0 {
			return operation.Source.Line
		}
	}
	return 1
}
