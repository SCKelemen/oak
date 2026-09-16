package machine

import (
	"fmt"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
)

// The RV64 OptIR selector allocates only caller-saved integer registers.
// x31/t6 is absent from ordinary coloring because it breaks parallel-copy
// cycles and provides the temporary low half when a constant needs more than
// one `li`. A pressured fallback also reserves x30/t5 as its second scratch;
// keeping it in the strict pool preserves the no-spill selector's capacity.
var optIRRV64Registers = []int{5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30}
var optIRRV64SpillRegisters = []int{5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29}

const (
	optIRRV64SpillScratchA = 30
	optIRRV64CopyScratch   = 31
	optIRRV64MaxFrame      = 2032
)

// LowerOptIRRV64 selects an admitted RV64 body from a verified optimized
// OptIR CFG. Its vocabulary is deliberately closed: Bool and fixed-width
// integer constants, copies, widening casts, total arithmetic, comparisons,
// branches, SSA edge arguments, and a deliberately narrow class of direct
// scalar calls. Other effects, trapping operations, memory, stack arguments,
// values live across calls, broad spill-loop shapes, and unsupported spill
// pressure refuse the candidate. On acyclic spill paths, independently
// verified cheap constants may be reconstructed instead of stored.
//
// RV64's 32-bit instructions sign-extend their result to XLEN. Oak therefore
// keeps both i32 and u32 in that canonical W-value representation; only a
// later widening of u32 to u64 explicitly clears the high half. The native
// candidate search must still seam-check and translation-validate the body
// before it may ship.
func LowerOptIRRV64(cfg optir.CFG, template *asm.Function) (*asm.Function, error) {
	return lowerOptIRRV64(cfg, template, optIRRV64Registers, optIRRV64SpillRegisters)
}

// LowerOptIRRV64WithRegionMemory is the low-level region-model entry. It
// independently checks exact RegionMemorySSA evidence, but the caller owns the
// region model; production source lowering uses
// LowerOptIRRV64WithCheckedRegionMemory instead.
func LowerOptIRRV64WithRegionMemory(
	cfg optir.CFG,
	template *asm.Function,
	metadata optir.RegionMemoryMetadata,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
) (*asm.Function, error) {
	memory, err := validateOptIRRegionMemory(cfg, template, metadata, memorySSA, bindings)
	if err != nil {
		return nil, err
	}
	return lowerOptIRRV64Selection(cfg, template, optIRRV64Registers, optIRRV64SpillRegisters, memory)
}

// LowerOptIRRV64WithCheckedRegionMemory is the production compiler entry:
// checked source authority must project to the exact final CFG before the
// independently verified RegionMemorySSA selector may emit an access.
func LowerOptIRRV64WithCheckedRegionMemory(
	cfg optir.CFG,
	template *asm.Function,
	authority optir.CheckedMemoryAuthority,
	projection optir.CheckedMemoryProjection,
	memorySSA optir.RegionMemorySSA,
	bindings map[optir.RegionID]OptIRRegionGlobal,
) (*asm.Function, error) {
	memory, err := validateCheckedOptIRRegionMemory(cfg, template, authority, projection, memorySSA, bindings)
	if err != nil {
		return nil, err
	}
	return lowerOptIRRV64Selection(cfg, template, optIRRV64Registers, optIRRV64SpillRegisters, memory)
}

func lowerOptIRRV64WithRegisters(cfg optir.CFG, template *asm.Function, registers []int) (*asm.Function, error) {
	return lowerOptIRRV64(cfg, template, registers, registers)
}

func lowerOptIRRV64(cfg optir.CFG, template *asm.Function, strictRegisters, spillRegisters []int) (*asm.Function, error) {
	return lowerOptIRRV64Selection(cfg, template, strictRegisters, spillRegisters, nil)
}

func lowerOptIRRV64Selection(cfg optir.CFG, template *asm.Function, strictRegisters, spillRegisters []int, memory *optIRRegionMemorySelection) (*asm.Function, error) {
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
	colors := map[optir.ValueID]int{}
	liveOut := map[optir.BlockID][]optir.ValueID{}
	spills := map[optir.ValueID]optir.SpillSlotID{}
	rematerializations := map[optir.ValueID]optir.RematerializationDecision{}
	spillLayout := optIRRV64SpillLayout{Offsets: map[optir.SpillSlotID]int64{}}
	coloring, coloringErr := optir.ColorRegisters(cfg, strictRegisters, fixed)
	if coloringErr == nil {
		colors, liveOut = coloring.Colors, coloring.LiveOut
	} else {
		if err := validateOptIRRV64SpillScratches(spillRegisters, []int{optIRRV64SpillScratchA, optIRRV64CopyScratch}); err != nil {
			return nil, err
		}
		plan, planFixed, planErr := planOptIRSpillsKeepingCanonicalLoopCondition(cfg, spillRegisters, fixed)
		if planErr != nil {
			return nil, fmt.Errorf("machine: OptIR RV64 allocation: %v; spill plan: %w", coloringErr, planErr)
		}
		if err := optir.VerifyRegisterPlan(cfg, spillRegisters, planFixed, plan); err != nil {
			return nil, fmt.Errorf("machine: OptIR RV64 spill-plan evidence: %w", err)
		}
		if err := validateOptIRRV64SpillCFGSelection(cfg, plan, memory); err != nil {
			return nil, err
		}
		rematerializations, err = optIRRV64Rematerializations(cfg, spillRegisters, planFixed, plan)
		if err != nil {
			return nil, err
		}
		spillLayout, err = layoutOptIRRV64Spills(plan, rematerializations, optIRRV64MaxFrame)
		if err != nil {
			return nil, err
		}
		colors, liveOut, spills = plan.Colors, plan.LiveOut, plan.Spills
	}
	calls, err := optIRRV64Calls(cfg, template, types, liveOut)
	if err != nil {
		return nil, err
	}
	if memory != nil && len(calls) != 0 && !memory.admitsNoModRefCalls(cfg) {
		return nil, fmt.Errorf("machine: OptIR RV64 region memory call lacks authenticated no-ModRef evidence")
	}
	spillFrame := spillLayout.Frame
	frame, raOffset, err := composeOptIRRV64Frame(spillFrame, len(calls) != 0)
	if err != nil {
		return nil, err
	}
	layout, err := optir.AnalyzeBlockLayout(cfg)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR RV64 block layout: %w", err)
	}
	if err := optir.VerifyBlockLayout(cfg, layout); err != nil {
		return nil, fmt.Errorf("machine: OptIR RV64 block layout evidence: %w", err)
	}

	selector := &optIRRV64Selector{
		cfg: cfg, types: types, colors: colors, spills: spills, spillOffsets: spillLayout.Offsets,
		rematerializations: rematerializations, definitions: optIRRV64Definitions(cfg),
		frame: frame, raOffset: raOffset,
		labels: map[optir.BlockID]string{}, written: map[int]bool{}, calls: calls, order: layout.Order,
		memory: memory, globals: map[string]asm.Global{},
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
	out.Frame = selector.frame
	out.System = false
	out.Globals = cloneOptIRSelectedGlobals(selector.globals)
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
	cfg                optir.CFG
	types              map[optir.ValueID]optir.Type
	colors             map[optir.ValueID]int
	spills             map[optir.ValueID]optir.SpillSlotID
	spillOffsets       map[optir.SpillSlotID]int64
	rematerializations map[optir.ValueID]optir.RematerializationDecision
	definitions        map[optir.ValueID]optir.Operation
	frame              int64
	raOffset           int64
	labels             map[optir.BlockID]string
	items              []asm.Item
	written            map[int]bool
	calls              map[optir.ValueID]string
	edges              int
	order              []optir.BlockID
	memory             *optIRRegionMemorySelection
	globals            map[string]asm.Global
}

func (selector *optIRRV64Selector) lower() error {
	for index, id := range selector.order {
		block := optIRBlock(selector.cfg, id)
		if block == nil {
			return fmt.Errorf("machine: OptIR layout names missing block %d", id)
		}
		line := optIRBlockLine(*block)
		selector.items = append(selector.items, asm.Label{Name: selector.labels[block.ID], Line: line})
		if block.ID == selector.cfg.Entry {
			if selector.frame != 0 {
				sp := optIRRV64SP()
				selector.emit("addi", line, sp, sp, asm.Immediate{Value: -selector.frame})
			}
			if len(selector.calls) != 0 {
				sp := optIRRV64SP()
				selector.emit("sd", line, optIRRV64Register(1), asm.Memory{Base: sp, Offset: selector.raOffset, Mode: asm.MemOffset})
			}
			// Do not let unspecified ABI padding become part of an Oak value.
			// Bool retains one bit; narrow integers are restored to their
			// signed or unsigned canonical representation before first use.
			for _, parameter := range block.Parameters {
				selector.normalize(selector.register(parameter.ID), parameter.Type, line)
			}
		}
		for operationIndex, operation := range block.Operations {
			site := optir.OperationSite{Block: block.ID, Index: operationIndex}
			if err := selector.operation(operation, site); err != nil {
				return fmt.Errorf("machine: OptIR block %d operation %s: %w", block.ID, operation.Code, err)
			}
		}
		next, hasNext := optir.BlockID(0), index+1 < len(selector.order)
		if hasNext {
			next = selector.order[index+1]
		}
		if err := selector.terminator(*block, next, hasNext, line); err != nil {
			return fmt.Errorf("machine: OptIR block %d terminator: %w", block.ID, err)
		}
	}
	return nil
}

func (selector *optIRRV64Selector) operation(operation optir.Operation, site optir.OperationSite) error {
	if operation.Code == optir.OpLoadRegion {
		return selector.regionLoad(operation, site)
	}
	if operation.Code == optir.OpStoreRegion {
		return selector.regionStore(operation, site)
	}
	if len(operation.Results) == 1 {
		if decision, rematerialized := selector.rematerializations[operation.Results[0].ID]; rematerialized {
			if decision.Code != operation.Code {
				return fmt.Errorf("rematerialization decision for value %d names %s, got %s", operation.Results[0].ID, decision.Code, operation.Code)
			}
			return nil
		}
	}
	if len(selector.spills) == 0 {
		return selector.registerOperation(operation)
	}
	if operation.Code == optir.OpCall {
		return selector.call(operation)
	}
	line := operation.Source.Line
	if line <= 0 && len(operation.Results) != 0 {
		line = operation.Results[0].Source.Line
	}
	original := map[optir.ValueID]int{}
	loaded := map[optir.ValueID]int{}
	nextScratch := optIRRV64SpillScratchA
	for _, operand := range operation.Operands {
		location, err := selector.valueLocation(operand)
		if err != nil {
			return err
		}
		if location.slot == 0 && location.rematerialized == 0 {
			continue
		}
		if _, exists := loaded[operand]; exists {
			continue
		}
		if nextScratch > optIRRV64CopyScratch {
			return fmt.Errorf("operation %s needs more than two spilled operands", operation.Code)
		}
		original[operand] = selector.colors[operand]
		selector.colors[operand] = nextScratch
		loaded[operand] = nextScratch
		if err := selector.readLocation(location, nextScratch, selector.types[operand], line); err != nil {
			return err
		}
		nextScratch++
	}
	var spilledResult optir.Value
	if len(operation.Results) == 1 {
		result := operation.Results[0]
		if _, spilled := selector.spills[result.ID]; spilled {
			spilledResult = result
			original[result.ID] = selector.colors[result.ID]
			selector.colors[result.ID] = optIRRV64SpillScratchA
		}
	}
	err := selector.registerOperation(operation)
	if err == nil && spilledResult.ID != 0 {
		err = selector.storeSpill(spilledResult.ID, selector.register(spilledResult.ID), line)
	}
	for value := range original {
		delete(selector.colors, value)
	}
	return err
}

func (selector *optIRRV64Selector) regionLoad(operation optir.Operation, site optir.OperationSite) error {
	if selector.memory == nil {
		return fmt.Errorf("effectful operation %s", operation.Code)
	}
	binding, admitted := selector.memory.loads[site]
	if !admitted {
		return fmt.Errorf("region load at %d:%d has no admitted global binding", site.Block, site.Index)
	}
	if len(operation.Results) != 1 {
		return fmt.Errorf("region load at %d:%d has %d results, want one", site.Block, site.Index, len(operation.Results))
	}
	result := operation.Results[0]
	mnemonic, ok := optIRRV64RegionLoad(result.Type)
	if !ok {
		return fmt.Errorf("region load at %d:%d has unsupported type %s", site.Block, site.Index, result.Type)
	}
	line := operation.Source.Line
	if line <= 0 {
		line = result.Source.Line
	}
	location, err := selector.valueLocation(result.ID)
	if err != nil {
		return err
	}
	if location.rematerialized != 0 {
		return fmt.Errorf("region load result %d is unexpectedly rematerialized", result.ID)
	}
	destination := location.register
	if location.slot != 0 {
		destination = optIRRV64SpillScratchA
	}
	selector.emit("la", line, optIRRV64Register(optIRRV64CopyScratch), asm.Symbol{Name: binding.Symbol})
	selector.emit(mnemonic, line, optIRRV64Register(destination), asm.Memory{Base: optIRRV64Register(optIRRV64CopyScratch)})
	selector.written[optIRRV64CopyScratch] = true
	selector.written[destination] = true
	if location.slot != 0 {
		if err := selector.storeSpillSlot(location.slot, destination, result.Type, line); err != nil {
			return err
		}
	}
	selector.globals[binding.Symbol] = binding.Global
	return nil
}

func (selector *optIRRV64Selector) regionStore(operation optir.Operation, site optir.OperationSite) error {
	if selector.memory == nil {
		return fmt.Errorf("effectful operation %s", operation.Code)
	}
	binding, admitted := selector.memory.stores[site]
	if !admitted {
		return fmt.Errorf("region store at %d:%d has no admitted global binding", site.Block, site.Index)
	}
	line := operation.Source.Line
	source, err := selector.readValue(operation.Operands[0], optIRRV64SpillScratchA, line)
	if err != nil {
		return err
	}
	selector.emit("la", line, optIRRV64Register(optIRRV64CopyScratch), asm.Symbol{Name: binding.Symbol})
	mnemonic := map[int]string{8: "sb", 16: "sh", 32: "sw", 64: "sd"}[binding.Global.Bits]
	selector.emit(mnemonic, line, optIRRV64Register(source), asm.Memory{Base: optIRRV64Register(optIRRV64CopyScratch)})
	selector.written[optIRRV64CopyScratch] = true
	selector.globals[binding.Symbol] = binding.Global
	return nil
}

func optIRRV64RegionLoad(typ optir.Type) (string, bool) {
	switch typ {
	case optir.TypeBool:
		// Bool occupies its canonical 32-bit package cell. The verifier
		// narrows that cell to the one-bit Oak value before extending it.
		return "lw", true
	case "u8":
		return "lbu", true
	case "i8":
		return "lb", true
	case "u16":
		return "lhu", true
	case "i16":
		return "lh", true
	case "u32", "i32":
		// Oak's RV64 W representation is sign-extended for both types;
		// widening u32 explicitly clears the upper half later.
		return "lw", true
	case "u64", "i64":
		return "ld", true
	default:
		return "", false
	}
}

func (selector *optIRRV64Selector) registerOperation(operation optir.Operation) error {
	if operation.Code != optir.OpCall && len(operation.Effects) != 0 {
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
	case optir.OpCall:
		return selector.call(operation)
	default:
		return fmt.Errorf("operation %s is outside the closed selector vocabulary", operation.Code)
	}
}

func (selector *optIRRV64Selector) call(operation optir.Operation) error {
	if len(operation.Results) != 1 {
		return fmt.Errorf("call has %d results, want one", len(operation.Results))
	}
	result := operation.Results[0]
	callee, admitted := selector.calls[result.ID]
	if !admitted {
		return fmt.Errorf("call is outside the admitted direct-call set")
	}
	line := operation.Source.Line
	if line <= 0 {
		line = result.Source.Line
	}
	moves := make([]optIRRV64LocationMove, 0, len(operation.Operands))
	for index, operand := range operation.Operands {
		destination := optIRRV64Location{register: 10 + index}
		source, err := selector.valueLocation(operand)
		if err != nil {
			return err
		}
		if destination != source {
			moves = append(moves, optIRRV64LocationMove{destination: destination, source: source, typ: selector.types[operand]})
		}
	}
	if err := selector.emitLocationCopies(moves, line); err != nil {
		return err
	}
	selector.emit("call", line, asm.Symbol{Name: callee})

	destination, err := selector.valueLocation(result.ID)
	if err != nil {
		return err
	}
	if destination.slot == 0 {
		selector.move(destination.register, 10, line)
		selector.normalize(destination.register, result.Type, line)
		return nil
	}
	selector.normalize(10, result.Type, line)
	return selector.storeSpillSlot(destination.slot, 10, result.Type, line)
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

func (selector *optIRRV64Selector) terminator(block optir.Block, next optir.BlockID, hasNext bool, line int) error {
	switch terminator := block.Terminator; terminator.Kind {
	case optir.TerminatorReturn:
		if len(terminator.Values) != 1 {
			return fmt.Errorf("return has %d values", len(terminator.Values))
		}
		value := terminator.Values[0]
		if selector.types[value] != optir.Type("()") {
			register, err := selector.readValue(value, optIRRV64SpillScratchA, line)
			if err != nil {
				return err
			}
			selector.move(10, register, line)
		}
		if len(selector.calls) != 0 {
			sp := optIRRV64SP()
			selector.emit("ld", line, optIRRV64Register(1), asm.Memory{Base: sp, Offset: selector.raOffset, Mode: asm.MemOffset})
		}
		if selector.frame != 0 {
			sp := optIRRV64SP()
			selector.emit("addi", line, sp, sp, asm.Immediate{Value: selector.frame})
		}
		selector.emit("ret", line)
		return nil
	case optir.TerminatorBranch:
		if err := selector.edgeCopies(terminator.True, line); err != nil {
			return err
		}
		if !hasNext || terminator.True.Target != next {
			selector.emit("j", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		}
		return nil
	case optir.TerminatorCondBranch:
		if selector.types[terminator.Condition] != optir.TypeBool {
			return fmt.Errorf("condition %d is not Bool", terminator.Condition)
		}
		condition, err := selector.readValue(terminator.Condition, optIRRV64SpillScratchA, line)
		if err != nil {
			return err
		}
		trueMoves, err := selector.edgeMoves(terminator.True)
		if err != nil {
			return err
		}
		falseMoves, err := selector.edgeMoves(terminator.False)
		if err != nil {
			return err
		}
		if len(trueMoves) == 0 && len(falseMoves) == 0 {
			trueTarget, falseTarget := terminator.True.Target, terminator.False.Target
			switch {
			case trueTarget == falseTarget:
				if !hasNext || trueTarget != next {
					selector.emit("j", line, asm.Symbol{Name: selector.labels[trueTarget]})
				}
			case hasNext && trueTarget == next:
				selector.emit("beqz", line, optIRRV64Register(condition), asm.Symbol{Name: selector.labels[falseTarget]})
			case hasNext && falseTarget == next:
				selector.emit("bnez", line, optIRRV64Register(condition), asm.Symbol{Name: selector.labels[trueTarget]})
			default:
				selector.emit("bnez", line, optIRRV64Register(condition), asm.Symbol{Name: selector.labels[trueTarget]})
				selector.emit("j", line, asm.Symbol{Name: selector.labels[falseTarget]})
			}
			return nil
		}
		trueLabel := selector.edgeLabel(block.ID, "true")
		falseLabel := selector.edgeLabel(block.ID, "false")
		selector.emit("bnez", line, optIRRV64Register(condition), asm.Symbol{Name: trueLabel})
		selector.emit("j", line, asm.Symbol{Name: falseLabel})
		selector.items = append(selector.items, asm.Label{Name: trueLabel, Line: line})
		if err := selector.emitLocationCopies(trueMoves, line); err != nil {
			return err
		}
		selector.emit("j", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		selector.items = append(selector.items, asm.Label{Name: falseLabel, Line: line})
		if err := selector.emitLocationCopies(falseMoves, line); err != nil {
			return err
		}
		selector.emit("j", line, asm.Symbol{Name: selector.labels[terminator.False.Target]})
		return nil
	default:
		return fmt.Errorf("unsupported terminator %s", terminator.Kind)
	}
}

type optIRRV64Location struct {
	register       int
	slot           optir.SpillSlotID
	rematerialized optir.ValueID
}

type optIRRV64LocationMove struct {
	destination optIRRV64Location
	source      optIRRV64Location
	typ         optir.Type
}

func (selector *optIRRV64Selector) valueLocation(value optir.ValueID) (optIRRV64Location, error) {
	register, colored := selector.colors[value]
	slot, spilled := selector.spills[value]
	if colored {
		if spilled {
			return optIRRV64Location{}, fmt.Errorf("value %d is both colored and spilled", value)
		}
		return optIRRV64Location{register: register}, nil
	}
	if _, rematerialized := selector.rematerializations[value]; rematerialized {
		return optIRRV64Location{rematerialized: value}, nil
	}
	if !spilled {
		return optIRRV64Location{}, fmt.Errorf("value %d does not have an RV64 machine location", value)
	}
	if slot == 0 {
		return optIRRV64Location{}, fmt.Errorf("value %d has invalid RV64 spill slot zero", value)
	}
	if _, exists := selector.spillOffsets[slot]; !exists {
		return optIRRV64Location{}, fmt.Errorf("value %d names missing RV64 spill slot %d", value, slot)
	}
	return optIRRV64Location{slot: slot}, nil
}

func (selector *optIRRV64Selector) readValue(value optir.ValueID, scratch, line int) (int, error) {
	location, err := selector.valueLocation(value)
	if err != nil {
		return 0, err
	}
	if location.slot == 0 {
		if location.rematerialized != 0 {
			if err := selector.emitRematerialized(location.rematerialized, scratch, line); err != nil {
				return 0, err
			}
			return scratch, nil
		}
		return location.register, nil
	}
	if err := selector.loadSpillSlot(location.slot, scratch, selector.types[value], line); err != nil {
		return 0, err
	}
	return scratch, nil
}

func (selector *optIRRV64Selector) readLocation(location optIRRV64Location, destination int, typ optir.Type, line int) error {
	if location.rematerialized != 0 {
		return selector.emitRematerialized(location.rematerialized, destination, line)
	}
	if location.slot != 0 {
		return selector.loadSpillSlot(location.slot, destination, typ, line)
	}
	selector.move(destination, location.register, line)
	return nil
}

func (selector *optIRRV64Selector) emitLocationMove(move optIRRV64LocationMove, line int) error {
	if move.destination.rematerialized != 0 {
		return fmt.Errorf("parallel copy cannot overwrite rematerialized value %d", move.destination.rematerialized)
	}
	if move.destination.slot == 0 {
		return selector.readLocation(move.source, move.destination.register, move.typ, line)
	}
	source := move.source.register
	if move.source.slot != 0 || move.source.rematerialized != 0 {
		source = optIRRV64SpillScratchA
		if err := selector.readLocation(move.source, source, move.typ, line); err != nil {
			return err
		}
	}
	return selector.storeSpillSlot(move.destination.slot, source, move.typ, line)
}

func (selector *optIRRV64Selector) edgeCopies(edge optir.Edge, line int) error {
	moves, err := selector.edgeMoves(edge)
	if err != nil {
		return err
	}
	return selector.emitLocationCopies(moves, line)
}

func (selector *optIRRV64Selector) edgeMoves(edge optir.Edge) ([]optIRRV64LocationMove, error) {
	target := optIRBlock(selector.cfg, edge.Target)
	if target == nil || len(target.Parameters) != len(edge.Arguments) {
		return nil, fmt.Errorf("invalid edge to block %d", edge.Target)
	}
	var moves []optIRRV64LocationMove
	for index, parameter := range target.Parameters {
		argument := edge.Arguments[index]
		if parameter.Type == optir.Type("()") {
			continue
		}
		if selector.types[argument] != parameter.Type {
			return nil, fmt.Errorf("edge to block %d passes %s to %s parameter %s", edge.Target, selector.types[argument], parameter.Type, parameter.Name)
		}
		destination, err := selector.valueLocation(parameter.ID)
		if err != nil {
			return nil, err
		}
		source, err := selector.valueLocation(argument)
		if err != nil {
			return nil, err
		}
		if destination != source {
			moves = append(moves, optIRRV64LocationMove{destination: destination, source: source, typ: parameter.Type})
		}
	}
	return moves, nil
}

func (selector *optIRRV64Selector) emitLocationCopies(moves []optIRRV64LocationMove, line int) error {
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
			if err := selector.emitLocationMove(move, line); err != nil {
				return err
			}
			moves = append(moves[:index], moves[index+1:]...)
			progress = true
			break
		}
		if progress {
			continue
		}

		// Preserve one old destination in t6, then make the cycle acyclic.
		// Slot-to-slot traffic uses t5, so it cannot overwrite this value.
		cycle := moves[0].destination
		if cycle.rematerialized != 0 {
			return fmt.Errorf("parallel-copy cycle cannot overwrite rematerialized value %d", cycle.rematerialized)
		}
		var cycleType optir.Type
		for _, move := range moves {
			if move.source == cycle {
				cycleType = move.typ
				break
			}
		}
		if cycleType == "" {
			return fmt.Errorf("parallel-copy cycle has no source for destination")
		}
		if err := selector.readLocation(cycle, optIRRV64CopyScratch, cycleType, line); err != nil {
			return err
		}
		scratch := optIRRV64Location{register: optIRRV64CopyScratch}
		for index := range moves {
			if moves[index].source == cycle {
				moves[index].source = scratch
			}
		}
	}
	return nil
}

func (selector *optIRRV64Selector) emitRematerialized(value optir.ValueID, destination, line int) error {
	decision, admitted := selector.rematerializations[value]
	operation, exists := selector.definitions[value]
	if !admitted || !exists || decision.Code != operation.Code || len(operation.Results) != 1 || operation.Results[0].ID != value ||
		len(operation.Operands) != 0 || len(operation.Effects) != 0 || len(operation.Facts) != 0 {
		return fmt.Errorf("value %d has no closed RV64 rematerialization definition", value)
	}
	if _, valid := optIRRV64RematerializationCost(operation); !valid {
		return fmt.Errorf("value %d has invalid RV64 rematerialization cost input", value)
	}
	switch operation.Code {
	case optir.OpConstBool:
		if operation.Results[0].Type != optir.TypeBool {
			return fmt.Errorf("malformed rematerialized Bool constant %d", value)
		}
		spelling, ok := optIRAttribute(operation, optir.AttributeValue)
		if !ok || spelling != "true" && spelling != "false" {
			return fmt.Errorf("invalid rematerialized Bool constant %d", value)
		}
		bits := int64(0)
		if spelling == "true" {
			bits = 1
		}
		selector.constant(destination, bits, line)
		return nil
	case optir.OpConstInt:
		spelling, ok := optIRAttribute(operation, optir.AttributeValue)
		if !ok {
			return fmt.Errorf("rematerialized integer constant %d has no value", value)
		}
		bits, err := optIRIntegerConstant(spelling, operation.Results[0].Type)
		if err != nil {
			return fmt.Errorf("invalid rematerialized %s constant %d", operation.Results[0].Type, value)
		}
		selector.constant(destination, optIRRV64Canonical(bits, operation.Results[0].Type), line)
		return nil
	default:
		return fmt.Errorf("value %d uses forbidden RV64 rematerialization operation %s", value, operation.Code)
	}
}

func optIRRV64Definitions(cfg optir.CFG) map[optir.ValueID]optir.Operation {
	definitions := map[optir.ValueID]optir.Operation{}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				definitions[result.ID] = operation
			}
		}
	}
	return definitions
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

func (selector *optIRRV64Selector) loadSpill(value optir.ValueID, register int, line int) error {
	slot, spilled := selector.spills[value]
	if !spilled {
		return fmt.Errorf("spilled value %d has no RV64 frame slot", value)
	}
	return selector.loadSpillSlot(slot, register, selector.types[value], line)
}

func (selector *optIRRV64Selector) loadSpillSlot(slot optir.SpillSlotID, register int, typ optir.Type, line int) error {
	offset, laidOut := selector.spillOffsets[slot]
	if slot == 0 || !laidOut {
		return fmt.Errorf("load names missing RV64 spill slot %d", slot)
	}
	mnemonic, ok := optIRRV64SpillLoad(typ)
	if !ok {
		return fmt.Errorf("RV64 spill slot %d has unsupported type %s", slot, typ)
	}
	selector.emit(mnemonic, line, optIRRV64Register(register), asm.Memory{Base: optIRRV64SP(), Offset: offset, Mode: asm.MemOffset})
	selector.written[register] = true
	selector.normalize(register, typ, line)
	return nil
}

func (selector *optIRRV64Selector) storeSpill(value optir.ValueID, register int, line int) error {
	slot, spilled := selector.spills[value]
	if !spilled {
		return fmt.Errorf("spilled value %d has no RV64 frame slot", value)
	}
	return selector.storeSpillSlot(slot, register, selector.types[value], line)
}

func (selector *optIRRV64Selector) storeSpillSlot(slot optir.SpillSlotID, register int, typ optir.Type, line int) error {
	offset, laidOut := selector.spillOffsets[slot]
	if slot == 0 || !laidOut {
		return fmt.Errorf("store names missing RV64 spill slot %d", slot)
	}
	mnemonic, ok := optIRRV64SpillStore(typ)
	if !ok {
		return fmt.Errorf("RV64 spill slot %d has unsupported type %s", slot, typ)
	}
	selector.emit(mnemonic, line, optIRRV64Register(register), asm.Memory{Base: optIRRV64SP(), Offset: offset, Mode: asm.MemOffset})
	return nil
}

func optIRRV64SpillLoad(typ optir.Type) (string, bool) {
	switch typ {
	case optir.TypeBool, "u8":
		return "lbu", true
	case "i8":
		return "lb", true
	case "u16":
		return "lhu", true
	case "i16":
		return "lh", true
	case "u32", "i32":
		// Both 32-bit Oak representations use RV64's canonical sign-extended
		// W value; u32 is zero-extended only by an explicit widening cast.
		return "lw", true
	case "u64", "i64":
		return "ld", true
	default:
		return "", false
	}
}

func optIRRV64SpillStore(typ optir.Type) (string, bool) {
	switch typ {
	case optir.TypeBool, "u8", "i8":
		return "sb", true
	case "u16", "i16":
		return "sh", true
	case "u32", "i32":
		return "sw", true
	case "u64", "i64":
		return "sd", true
	default:
		return "", false
	}
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

// optIRRV64Calls closes the first call subset before selection. Every
// allocatable register is caller-saved, so no non-unit value may be live
// immediately after a call other than that call's result. The backward scan
// combines block LiveOut evidence with local uses and does not infer
// preservation from a fortuitous physical color.
func optIRRV64Calls(cfg optir.CFG, template *asm.Function, types map[optir.ValueID]optir.Type, liveOut map[optir.BlockID][]optir.ValueID) (map[optir.ValueID]string, error) {
	calls := map[optir.ValueID]string{}
	for _, block := range cfg.Blocks {
		live := map[optir.ValueID]bool{}
		for _, value := range liveOut[block.ID] {
			live[value] = true
		}
		for _, value := range optIRTerminatorUses(block.Terminator) {
			live[value] = true
		}
		for index := len(block.Operations) - 1; index >= 0; index-- {
			operation := block.Operations[index]
			if operation.Code != optir.OpCall {
				for _, result := range operation.Results {
					delete(live, result.ID)
				}
				for _, operand := range operation.Operands {
					if types[operand] != optir.Type("()") {
						live[operand] = true
					}
				}
				continue
			}
			calleeName, result, err := optIRRV64Call(operation, template, types)
			if err != nil {
				return nil, fmt.Errorf("machine: OptIR block %d operation %s: %w", block.ID, operation.Code, err)
			}
			delete(live, result.ID)
			for value := range live {
				if types[value] != optir.Type("()") {
					return nil, fmt.Errorf("machine: OptIR block %d operation %s: value %d is live across a call", block.ID, operation.Code, value)
				}
			}
			calls[result.ID] = calleeName
			for _, operand := range operation.Operands {
				if types[operand] != optir.Type("()") {
					live[operand] = true
				}
			}
		}
	}
	return calls, nil
}

func optIRRV64Call(operation optir.Operation, template *asm.Function, types map[optir.ValueID]optir.Type) (string, optir.Value, error) {
	if len(operation.Results) != 1 || len(operation.Effects) != 1 || operation.Effects[0] != optir.EffectCall {
		return "", optir.Value{}, fmt.Errorf("call has malformed result or effect evidence")
	}
	calleeName, ok := optIRAttribute(operation, optir.AttributeCallee)
	if !ok || calleeName == "" {
		return "", optir.Value{}, fmt.Errorf("call has no unique direct callee")
	}
	callee := template.Callees[calleeName]
	if callee == nil || callee.Name == nil || callee.Name.Value != calleeName || callee.Body == nil || callee.Receiver != nil || len(callee.TypeParams) != 0 || callee.ExternSymbol != "" {
		return "", optir.Value{}, fmt.Errorf("call to %s is not a known direct Oak function", calleeName)
	}
	if len(operation.Operands) > 8 || len(callee.Parameters) > 8 {
		return "", optir.Value{}, fmt.Errorf("call to %s has more than eight scalar register arguments", calleeName)
	}
	if len(operation.Operands) != len(callee.Parameters) {
		return "", optir.Value{}, fmt.Errorf("call to %s has %d arguments, want %d", calleeName, len(operation.Operands), len(callee.Parameters))
	}
	for index, parameter := range callee.Parameters {
		if parameter == nil {
			return "", optir.Value{}, fmt.Errorf("call to %s has a missing parameter %d", calleeName, index+1)
		}
		parameterType, scalar := optIRRV64ScalarType(parameter.Type)
		if parameter.Variadic || !scalar || types[operation.Operands[index]] != parameterType {
			return "", optir.Value{}, fmt.Errorf("call to %s parameter %d is not a matching scalar", calleeName, index+1)
		}
	}
	result := operation.Results[0]
	returnType, scalar := optIRRV64ScalarType(callee.ReturnType)
	if !scalar || result.Type != returnType {
		return "", optir.Value{}, fmt.Errorf("call to %s result %s does not match scalar return %s", calleeName, result.Type, returnType)
	}
	return calleeName, result, nil
}

func optIRRV64ScalarType(expression ast.Expression) (optir.Type, bool) {
	identifier, ok := expression.(*ast.Identifier)
	if !ok || identifier == nil {
		return "", false
	}
	typ := optir.Type(identifier.Value)
	if typ == optir.TypeBool {
		return typ, true
	}
	_, _, ok = optIRRV64Type(typ)
	return typ, ok
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

func optIRRV64SP() asm.Register {
	return asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1}
}
