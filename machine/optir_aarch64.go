package machine

import (
	"fmt"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
)

// The OptIR selector uses only caller-saved general registers. x8 is the
// indirect-result register, x17 is reserved for parallel-copy cycles, and x18
// is platform-reserved. A deliberately narrow direct-call seam admits calls
// only when no other allocated value must survive them.
var optIRArm64Registers = []int{0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16}

var optIRArm64SpillRegisters = []int{0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14}

const (
	optIRSpillOperand0 = 15
	optIRSpillOperand1 = 16
	optIRCopyScratch   = 17
)

// LowerOptIRArm64 selects an admitted AArch64 body from a verified optimized
// OptIR CFG. It deliberately supports a small closed vocabulary: Bool and
// fixed-width integer constants, copies, widening casts, total arithmetic,
// comparisons, branches, SSA edge arguments, and scalar direct calls with no
// unrelated live-across value. Excess register pressure is materialized through
// a verified, bounded scalar spill plan. Other effects, trapping operations,
// and stack arguments refuse the candidate.
// Narrow integers stay normalized in W registers: unsigned values are
// zero-extended and signed values are sign-extended within the word. The native
// search independently seam-checks and translation-validates every returned
// body before it may ship.
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
	allocation, err := optIRArm64Allocate(cfg, types, fixed)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR AArch64 allocation: %w", err)
	}
	hasCalls, err := validateOptIRArm64Calls(cfg, allocation.liveOut, template.Callees)
	if err != nil {
		return nil, err
	}
	spillFrame, frame := allocation.frame, allocation.frame
	if hasCalls {
		if spillFrame > optIRArm64MaxSpillFrame-16 {
			return nil, fmt.Errorf("machine: OptIR AArch64 spill/call frame needs more than %d bytes", optIRArm64MaxSpillFrame)
		}
		frame += 16
	}
	layout, err := optir.AnalyzeBlockLayout(cfg)
	if err != nil {
		return nil, fmt.Errorf("machine: OptIR AArch64 block layout: %w", err)
	}
	if err := optir.VerifyBlockLayout(cfg, layout); err != nil {
		return nil, fmt.Errorf("machine: OptIR AArch64 block layout evidence: %w", err)
	}

	selector := &optIRArm64Selector{
		cfg: cfg, types: types, colors: allocation.colors, spills: allocation.spills,
		slots: allocation.slots, spillFrame: spillFrame, frame: frame,
		labels: map[optir.BlockID]string{}, written: map[int]bool{}, order: layout.Order,
		hasCalls: hasCalls,
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
	out.Frame = selector.frame
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
	cfg        optir.CFG
	types      map[optir.ValueID]optir.Type
	colors     map[optir.ValueID]int
	spills     map[optir.ValueID]optir.SpillSlotID
	slots      map[optir.SpillSlotID]optIRArm64FrameSlot
	spillFrame int64
	frame      int64
	labels     map[optir.BlockID]string
	items      []asm.Item
	written    map[int]bool
	edges      int
	order      []optir.BlockID
	hasCalls   bool
}

func (selector *optIRArm64Selector) lower() error {
	if selector.spillFrame != 0 {
		entry := optIRBlock(selector.cfg, selector.cfg.Entry)
		if entry == nil {
			return fmt.Errorf("machine: OptIR stack frame has no entry block %d", selector.cfg.Entry)
		}
		selector.emit("sub", optIRBlockLine(*entry), optIRSP(), optIRSP(), asm.Immediate{Value: selector.frame})
	}
	for index, id := range selector.order {
		block := optIRBlock(selector.cfg, id)
		if block == nil {
			return fmt.Errorf("machine: OptIR layout names missing block %d", id)
		}
		line := optIRBlockLine(*block)
		selector.items = append(selector.items, asm.Label{Name: selector.labels[block.ID], Line: line})
		if block.ID == selector.cfg.Entry {
			if selector.hasCalls {
				frame := asm.Memory{Base: optIRSP(), Offset: selector.spillFrame}
				if selector.spillFrame == 0 {
					frame.Offset = -16
					frame.Mode = asm.MemPreIndex
				}
				selector.emit("str", line, arm64X(30), frame)
			}
			// AAPCS64 leaves the register bits above narrow scalar arguments
			// unspecified. Establish the representation invariant before any
			// selected operation can observe them.
			for _, parameter := range block.Parameters {
				register, ok := selector.colors[parameter.ID]
				if !ok {
					return fmt.Errorf("machine: OptIR entry parameter %d is not register-resident", parameter.ID)
				}
				selector.normalize(register, parameter.Type, line)
			}
		}
		for _, operation := range block.Operations {
			if err := selector.operation(operation); err != nil {
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

func (selector *optIRArm64Selector) operation(operation optir.Operation) error {
	if operation.Code == optir.OpCall {
		return selector.call(operation)
	}
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
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		selector.constant(destination, bits, 32, line)
		return selector.commitValue(result.ID, destination, line)
	case optir.OpConstInt:
		_, _, ok := optIRArm64Type(result.Type)
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
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		selector.constant(destination, value, optIRBits(result.Type), line)
		return selector.commitValue(result.ID, destination, line)
	case optir.OpCopy:
		if len(operation.Operands) != 1 || selector.types[operation.Operands[0]] != result.Type || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed copy")
		}
		source, err := selector.readValue(operation.Operands[0], optIRSpillOperand0, line)
		if err != nil {
			return err
		}
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		selector.move(destination, source, optIRBits(result.Type), line)
		return selector.commitValue(result.ID, destination, line)
	case optir.OpCastInt:
		if len(operation.Operands) != 1 || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed integer cast")
		}
		source, err := selector.readValue(operation.Operands[0], optIRSpillOperand0, line)
		if err != nil {
			return err
		}
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		if err := selector.cast(destination, result.Type, source, selector.types[operation.Operands[0]], line); err != nil {
			return err
		}
		return selector.commitValue(result.ID, destination, line)
	case optir.OpBoolNot:
		if len(operation.Operands) != 1 || result.Type != optir.TypeBool || selector.types[operation.Operands[0]] != optir.TypeBool || len(operation.Attributes) != 0 {
			return fmt.Errorf("malformed Bool negation")
		}
		source, err := selector.readValue(operation.Operands[0], optIRSpillOperand0, line)
		if err != nil {
			return err
		}
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		selector.emit("eor", line, optIRW(destination), optIRW(source), asm.Immediate{Value: 1})
		return selector.commitValue(result.ID, destination, line)
	case optir.OpIntNeg:
		if err := selector.sameIntegerOperation(operation, 1); err != nil {
			return err
		}
		source, err := selector.readValue(operation.Operands[0], optIRSpillOperand0, line)
		if err != nil {
			return err
		}
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		selector.emit("neg", line, optIRRegister(destination, optIRBits(result.Type)), optIRRegister(source, optIRBits(result.Type)))
		selector.normalize(destination, result.Type, line)
		return selector.commitValue(result.ID, destination, line)
	case optir.OpIntAdd, optir.OpIntSub, optir.OpIntMul, optir.OpIntAnd, optir.OpIntOr, optir.OpIntXor:
		if err := selector.sameIntegerOperation(operation, 2); err != nil {
			return err
		}
		mnemonic := map[string]string{
			optir.OpIntAdd: "add", optir.OpIntSub: "sub", optir.OpIntMul: "mul",
			optir.OpIntAnd: "and", optir.OpIntOr: "orr", optir.OpIntXor: "eor",
		}[operation.Code]
		left, err := selector.readValue(operation.Operands[0], optIRSpillOperand0, line)
		if err != nil {
			return err
		}
		right, err := selector.readValue(operation.Operands[1], optIRSpillOperand1, line)
		if err != nil {
			return err
		}
		destination, err := selector.writeValue(result.ID, optIRCopyScratch)
		if err != nil {
			return err
		}
		bits := optIRBits(result.Type)
		selector.emit(mnemonic, line, optIRRegister(destination, bits), optIRRegister(left, bits), optIRRegister(right, bits))
		selector.normalize(destination, result.Type, line)
		return selector.commitValue(result.ID, destination, line)
	case optir.OpEqual, optir.OpNotEqual, optir.OpLess, optir.OpLessEqual, optir.OpGreater, optir.OpGreaterEqual:
		return selector.compare(operation, line)
	default:
		return fmt.Errorf("operation %s is outside the closed selector vocabulary", operation.Code)
	}
}

func (selector *optIRArm64Selector) call(operation optir.Operation) error {
	if len(operation.Results) != 1 {
		return fmt.Errorf("call has %d results, want one", len(operation.Results))
	}
	callee, ok := optIRAttribute(operation, optir.AttributeCallee)
	if !ok {
		return fmt.Errorf("call does not name exactly one callee")
	}
	line := operation.Source.Line
	if line <= 0 {
		line = operation.Results[0].Source.Line
	}
	var moves []optIRLocationMove
	for index, operand := range operation.Operands {
		destination := optIRValueLocation{register: index}
		source, err := selector.valueLocation(operand)
		if err != nil {
			return err
		}
		if destination != source {
			moves = append(moves, optIRLocationMove{destination: destination, source: source, typ: selector.types[operand]})
		}
	}
	if err := selector.emitEdgeCopies(moves, line); err != nil {
		return err
	}
	selector.emit("bl", line, asm.Symbol{Name: callee})
	result := operation.Results[0]
	destination, err := selector.writeValue(result.ID, optIRCopyScratch)
	if err != nil {
		return err
	}
	selector.move(destination, 0, optIRBits(result.Type), line)
	selector.normalize(destination, result.Type, line)
	return selector.commitValue(result.ID, destination, line)
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

func (selector *optIRArm64Selector) cast(destination int, resultType optir.Type, source int, fromType optir.Type, line int) error {
	toBits, _, toOK := optIRArm64Type(resultType)
	fromBits, fromSigned, fromOK := optIRArm64Type(fromType)
	if !toOK || !fromOK || fromBits > toBits {
		return fmt.Errorf("unsupported value-preserving cast %s to %s", fromType, resultType)
	}
	switch {
	case fromBits == toBits:
		selector.move(destination, source, optIRBits(resultType), line)
	case fromBits == 8 && fromSigned:
		selector.emit("sxtb", line, optIRRegister(destination, optIRBits(resultType)), optIRW(source))
	case fromBits == 16 && fromSigned:
		selector.emit("sxth", line, optIRRegister(destination, optIRBits(resultType)), optIRW(source))
	case fromBits == 8:
		// UXTB writes W even when the destination value is 64-bit; a W
		// write also clears the upper half of the corresponding X register.
		selector.emit("uxtb", line, optIRW(destination), optIRW(source))
	case fromBits == 16:
		selector.emit("uxth", line, optIRW(destination), optIRW(source))
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
	left, err := selector.readValue(operation.Operands[0], optIRSpillOperand0, line)
	if err != nil {
		return err
	}
	right, err := selector.readValue(operation.Operands[1], optIRSpillOperand1, line)
	if err != nil {
		return err
	}
	destination, err := selector.writeValue(operation.Results[0].ID, optIRCopyScratch)
	if err != nil {
		return err
	}
	selector.emit("cmp", line, optIRRegister(left, bits), optIRRegister(right, bits))
	selector.emit("cset", line, optIRW(destination), asm.Condition{Code: condition})
	return selector.commitValue(operation.Results[0].ID, destination, line)
}

func (selector *optIRArm64Selector) terminator(block optir.Block, next optir.BlockID, hasNext bool, line int) error {
	switch terminator := block.Terminator; terminator.Kind {
	case optir.TerminatorReturn:
		if len(terminator.Values) != 1 {
			return fmt.Errorf("return has %d values", len(terminator.Values))
		}
		value := terminator.Values[0]
		if selector.types[value] != optir.Type("()") {
			register, err := selector.readValue(value, optIRSpillOperand0, line)
			if err != nil {
				return err
			}
			selector.move(0, register, optIRBits(selector.types[value]), line)
		}
		if selector.hasCalls {
			frame := asm.Memory{Base: optIRSP(), Offset: selector.spillFrame}
			if selector.spillFrame == 0 {
				frame.Offset = 16
				frame.Mode = asm.MemPostIndex
			}
			selector.emit("ldr", line, arm64X(30), frame)
		}
		if selector.spillFrame != 0 {
			selector.emit("add", line, optIRSP(), optIRSP(), asm.Immediate{Value: selector.frame})
		}
		selector.emit("ret", line)
		return nil
	case optir.TerminatorBranch:
		if err := selector.edgeCopies(terminator.True, line); err != nil {
			return err
		}
		if !hasNext || terminator.True.Target != next {
			selector.emit("b", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		}
		return nil
	case optir.TerminatorCondBranch:
		if selector.types[terminator.Condition] != optir.TypeBool {
			return fmt.Errorf("condition %d is not Bool", terminator.Condition)
		}
		condition, err := selector.readValue(terminator.Condition, optIRSpillOperand0, line)
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
					selector.emit("b", line, asm.Symbol{Name: selector.labels[trueTarget]})
				}
			case hasNext && trueTarget == next:
				selector.emit("cbz", line, optIRW(condition), asm.Symbol{Name: selector.labels[falseTarget]})
			case hasNext && falseTarget == next:
				selector.emit("cbnz", line, optIRW(condition), asm.Symbol{Name: selector.labels[trueTarget]})
			default:
				selector.emit("cbnz", line, optIRW(condition), asm.Symbol{Name: selector.labels[trueTarget]})
				selector.emit("b", line, asm.Symbol{Name: selector.labels[falseTarget]})
			}
			return nil
		}
		trueLabel := selector.edgeLabel(block.ID, "true")
		falseLabel := selector.edgeLabel(block.ID, "false")
		selector.emit("cbnz", line, optIRW(condition), asm.Symbol{Name: trueLabel})
		selector.emit("b", line, asm.Symbol{Name: falseLabel})
		selector.items = append(selector.items, asm.Label{Name: trueLabel, Line: line})
		if err := selector.emitEdgeCopies(trueMoves, line); err != nil {
			return err
		}
		selector.emit("b", line, asm.Symbol{Name: selector.labels[terminator.True.Target]})
		selector.items = append(selector.items, asm.Label{Name: falseLabel, Line: line})
		if err := selector.emitEdgeCopies(falseMoves, line); err != nil {
			return err
		}
		selector.emit("b", line, asm.Symbol{Name: selector.labels[terminator.False.Target]})
		return nil
	default:
		return fmt.Errorf("unsupported terminator %s", terminator.Kind)
	}
}

type optIRValueLocation struct {
	register int
	slot     optir.SpillSlotID
}

type optIRLocationMove struct {
	destination optIRValueLocation
	source      optIRValueLocation
	typ         optir.Type
}

func (selector *optIRArm64Selector) edgeCopies(edge optir.Edge, line int) error {
	moves, err := selector.edgeMoves(edge)
	if err != nil {
		return err
	}
	return selector.emitEdgeCopies(moves, line)
}

func (selector *optIRArm64Selector) edgeMoves(edge optir.Edge) ([]optIRLocationMove, error) {
	target := optIRBlock(selector.cfg, edge.Target)
	if target == nil || len(target.Parameters) != len(edge.Arguments) {
		return nil, fmt.Errorf("invalid edge to block %d", edge.Target)
	}
	var moves []optIRLocationMove
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
			moves = append(moves, optIRLocationMove{destination: destination, source: source, typ: parameter.Type})
		}
	}
	return moves, nil
}

func (selector *optIRArm64Selector) emitEdgeCopies(moves []optIRLocationMove, line int) error {
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
		// A cycle: save one destination's old value, then replace every
		// use of it with the reserved scratch and continue acyclically.
		cycle := moves[0].destination
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
		if cycle.slot == 0 {
			// Preserve the strict register-only path's full-width cycle save.
			// Individual destinations still select their declared width.
			selector.move(optIRCopyScratch, cycle.register, 64, line)
		} else if err := selector.readLocation(cycle, optIRCopyScratch, cycleType, line); err != nil {
			return err
		}
		scratch := optIRValueLocation{register: optIRCopyScratch}
		for index := range moves {
			if moves[index].source == cycle {
				moves[index].source = scratch
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

func (selector *optIRArm64Selector) normalize(register int, typ optir.Type, line int) {
	if typ == optir.TypeBool {
		// AAPCS64 leaves the bits above a narrow argument unspecified. Oak
		// Bool is exactly 0 or 1, so retain only its represented bit before a
		// W-register branch or comparison can observe the rest of the word.
		selector.emit("and", line, optIRW(register), optIRW(register), asm.Immediate{Value: 1})
		return
	}
	bits, signed, ok := optIRArm64Type(typ)
	if !ok || bits >= 32 {
		return
	}
	mnemonic := map[int]string{8: "uxtb", 16: "uxth"}[bits]
	if signed {
		mnemonic = map[int]string{8: "sxtb", 16: "sxth"}[bits]
	}
	selector.emit(mnemonic, line, optIRW(register), optIRW(register))
}

func (selector *optIRArm64Selector) emit(mnemonic string, line int, operands ...asm.Operand) {
	selector.items = append(selector.items, asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: line})
	if mnemonic == "bl" {
		selector.written[30] = true
	}
	if len(operands) == 0 {
		return
	}
	if destination, ok := operands[0].(asm.Register); ok {
		switch mnemonic {
		case "mov", "movz", "movk", "sxtb", "sxth", "sxtw", "uxtb", "uxth", "eor", "neg", "add", "sub", "mul", "and", "orr", "cset",
			"ldr", "ldrb", "ldrh", "ldrsb", "ldrsh":
			if (destination.Class == asm.ClassW || destination.Class == asm.ClassX) && !destination.ZeroRegister() {
				selector.written[destination.Num] = true
			}
		}
	}
}

// validateOptIRArm64Calls closes the first call subset before selection. Every
// allocatable register is caller-saved, so a call is admissible only when its
// own result is the sole non-unit value live immediately after it. The
// backward scan combines block LiveOut evidence with local operation uses; it
// does not infer preservation from a fortuitous physical color.
func validateOptIRArm64Calls(cfg optir.CFG, liveOut map[optir.BlockID][]optir.ValueID, callees map[string]*ast.FunctionStatement) (bool, error) {
	types := optIRTypes(cfg)
	hasCalls := false
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
			if operation.Code == optir.OpCall {
				hasCalls = true
				if err := validateOptIRArm64Call(operation, types, callees); err != nil {
					return false, fmt.Errorf("machine: OptIR block %d operation %s: %w", block.ID, operation.Code, err)
				}
				for _, result := range operation.Results {
					delete(live, result.ID)
				}
				for value := range live {
					if types[value] != optir.Type("()") {
						return false, fmt.Errorf("machine: OptIR block %d operation %s: value %d is live across a call", block.ID, operation.Code, value)
					}
				}
			}
			for _, result := range operation.Results {
				delete(live, result.ID)
			}
			for _, operand := range operation.Operands {
				if types[operand] != optir.Type("()") {
					live[operand] = true
				}
			}
		}
	}
	return hasCalls, nil
}

func validateOptIRArm64Call(operation optir.Operation, types map[optir.ValueID]optir.Type, callees map[string]*ast.FunctionStatement) error {
	if len(operation.Results) != 1 {
		return fmt.Errorf("call has %d results, want one scalar result", len(operation.Results))
	}
	if len(operation.Operands) > 8 {
		return fmt.Errorf("call has %d arguments, want at most eight scalar register arguments", len(operation.Operands))
	}
	if len(operation.Effects) != 1 || operation.Effects[0] != optir.EffectCall {
		return fmt.Errorf("call must carry exactly the %s effect", optir.EffectCall)
	}
	name, ok := optIRAttribute(operation, optir.AttributeCallee)
	if !ok || name == "" {
		return fmt.Errorf("call does not name exactly one callee")
	}
	callee := callees[name]
	if callee == nil || callee.Name == nil || callee.Name.Value != name || callee.Body == nil || callee.Receiver != nil || len(callee.TypeParams) != 0 || callee.ExternSymbol != "" {
		return fmt.Errorf("call target %s is not a known direct Oak callee", name)
	}
	if len(callee.Parameters) != len(operation.Operands) {
		return fmt.Errorf("call to %s has %d arguments but its Oak signature has %d", name, len(operation.Operands), len(callee.Parameters))
	}
	for index, operand := range operation.Operands {
		if callee.Parameters[index] == nil || callee.Parameters[index].Variadic {
			return fmt.Errorf("call to %s has an unsupported parameter %d", name, index+1)
		}
		parameterType, scalar := optIRArm64ASTScalarType(callee.Parameters[index].Type)
		if !scalar || types[operand] != parameterType {
			return fmt.Errorf("call to %s argument %d has OptIR type %s but Oak type %s", name, index+1, types[operand], parameterType)
		}
	}
	resultType, scalar := optIRArm64ASTScalarType(callee.ReturnType)
	if !scalar || operation.Results[0].Type != resultType {
		return fmt.Errorf("call to %s result has OptIR type %s but Oak type %s", name, operation.Results[0].Type, resultType)
	}
	return nil
}

func optIRArm64ASTScalarType(expression ast.Expression) (optir.Type, bool) {
	identifier, ok := expression.(*ast.Identifier)
	if !ok || identifier == nil {
		return "", false
	}
	typ := optir.Type(identifier.Value)
	if typ == optir.TypeBool {
		return typ, true
	}
	_, _, ok = optIRArm64Type(typ)
	return typ, ok
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

func optIRBits(typ optir.Type) int {
	if typ == optir.TypeBool {
		return 32
	}
	bits, _, _ := optIRArm64Type(typ)
	if bits < 32 {
		return 32
	}
	return bits
}

func optIRIntegerConstant(spelling string, typ optir.Type) (uint64, error) {
	bits, signed, ok := optIRArm64Type(typ)
	if !ok {
		return 0, fmt.Errorf("non-integer type %s", typ)
	}
	if signed {
		value, err := strconv.ParseInt(spelling, 10, bits)
		return uint64(value), err
	}
	return strconv.ParseUint(spelling, 10, bits)
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

func optIRTerminatorUses(terminator optir.Terminator) []optir.ValueID {
	var out []optir.ValueID
	switch terminator.Kind {
	case optir.TerminatorReturn:
		out = append(out, terminator.Values...)
	case optir.TerminatorBranch:
		out = append(out, terminator.True.Arguments...)
	case optir.TerminatorCondBranch:
		out = append(out, terminator.Condition)
		out = append(out, terminator.True.Arguments...)
		out = append(out, terminator.False.Arguments...)
	}
	return out
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
