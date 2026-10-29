package optir

import (
	"fmt"
	"math"
	"strconv"
)

// StatefulMemory is deliberately partial: absent addresses are unmapped or
// uninitialized and cause a byte-access fault. This concrete regression model
// does not establish owner lifetime, grants, or physical nonaliasing. Those are
// premises of the separate StatefulCopy.Invocation refinement theorem.
type StatefulMemory map[uint64]uint8

type StatefulDescriptor struct {
	Base   uint64
	Length uint32
}

// StatefulRuntimeValue preserves logical types and real nested constructors.
// A descriptor or Result is never reinterpreted as an integer carrier.
type StatefulRuntimeValue struct {
	Type       Type
	Uint       uint32
	Bool       bool
	Descriptor StatefulDescriptor
	Variant    string
	Payload    *StatefulRuntimeValue
}

type StatefulExecutionOutcome string

const (
	StatefulReturned  StatefulExecutionOutcome = "returned"
	StatefulFault     StatefulExecutionOutcome = "fault"
	StatefulExhausted StatefulExecutionOutcome = "exhausted"
)

type StatefulCallResult struct {
	Function string
	Value    StatefulRuntimeValue
}

type StatefulExecution struct {
	Outcome StatefulExecutionOutcome
	Value   StatefulRuntimeValue
	Memory  StatefulMemory
	Calls   []StatefulCallResult
	Steps   uint64
	Fault   string
}

// ExecuteStatefulProgram interprets the admitted production CFG, including its
// actual non-inlined call. It takes an owned memory copy and executes operations
// generically: no operation invokes a reference copy implementation. One unit
// of IR fuel is consumed per operation and per terminator, including every
// callee operation/terminator; entry and edge parameter binding have no extra
// cost. Exhaustion and runtime faults are not DestinationTooSmall Results.
//
// This executable regression oracle is not a kernel proof, source-correctness
// claim, native ABI, or instruction-fuel claim.
func ExecuteStatefulProgram(p StatefulProgram, dst, src StatefulDescriptor, memory StatefulMemory, fuel uint64) (StatefulExecution, error) {
	if err := VerifyStatefulProgram(p); err != nil {
		return StatefulExecution{}, err
	}
	e := statefulExecutor{functions: map[string]CFG{}, memory: cloneStatefulMemory(memory), remaining: fuel}
	for _, f := range p.functions {
		e.functions[f.CFG.Name] = f.CFG
	}
	outcome, value := e.function(p.root, []StatefulRuntimeValue{{Type: TypeByteSpan, Descriptor: dst}, {Type: TypeByteView, Descriptor: src}})
	return StatefulExecution{Outcome: outcome, Value: cloneStatefulValue(value), Memory: e.memory, Calls: e.calls, Steps: fuel - e.remaining, Fault: e.fault}, nil
}

func cloneStatefulMemory(memory StatefulMemory) StatefulMemory {
	result := make(StatefulMemory, len(memory))
	for address, value := range memory {
		result[address] = value
	}
	return result
}
func cloneStatefulValue(value StatefulRuntimeValue) StatefulRuntimeValue {
	if value.Payload != nil {
		payload := cloneStatefulValue(*value.Payload)
		value.Payload = &payload
	}
	return value
}

type statefulExecutor struct {
	functions map[string]CFG
	memory    StatefulMemory
	remaining uint64
	calls     []StatefulCallResult
	fault     string
}

func (e *statefulExecutor) step() bool {
	if e.remaining == 0 {
		return false
	}
	e.remaining--
	return true
}
func (e *statefulExecutor) fail(reason string) (StatefulExecutionOutcome, StatefulRuntimeValue) {
	e.fault = reason
	return StatefulFault, StatefulRuntimeValue{}
}
func (e *statefulExecutor) function(name string, args []StatefulRuntimeValue) (StatefulExecutionOutcome, StatefulRuntimeValue) {
	cfg, exists := e.functions[name]
	if !exists {
		return e.fail("missing admitted callee")
	}
	blocks := map[BlockID]Block{}
	for _, b := range cfg.Blocks {
		blocks[b.ID] = b
	}
	block := blocks[cfg.Entry]
	if len(block.Parameters) != len(args) {
		return e.fail("call argument arity mismatch")
	}
	env := map[ValueID]StatefulRuntimeValue{}
	for i, p := range block.Parameters {
		if p.Type != args[i].Type {
			return e.fail("call argument type mismatch")
		}
		env[p.ID] = args[i]
	}
	for {
		for _, op := range block.Operations {
			if !e.step() {
				return StatefulExhausted, StatefulRuntimeValue{}
			}
			outcome, value := e.operation(op, env)
			if outcome != StatefulReturned {
				return outcome, value
			}
			if len(op.Results) == 1 {
				env[op.Results[0].ID] = value
			}
		}
		if !e.step() {
			return StatefulExhausted, StatefulRuntimeValue{}
		}
		term := block.Terminator
		var edge Edge
		switch term.Kind {
		case TerminatorReturn:
			if len(term.Values) != 1 {
				return e.fail("return arity mismatch")
			}
			value, exists := env[term.Values[0]]
			if !exists {
				return e.fail("undefined return value")
			}
			return StatefulReturned, value
		case TerminatorBranch:
			edge = term.True
		case TerminatorCondBranch:
			condition, exists := env[term.Condition]
			if !exists || condition.Type != TypeBool {
				return e.fail("invalid branch condition")
			}
			edge = term.False
			if condition.Bool {
				edge = term.True
			}
		default:
			return e.fail("unsupported terminator")
		}
		next, exists := blocks[edge.Target]
		if !exists || len(next.Parameters) != len(edge.Arguments) {
			return e.fail("invalid edge")
		}
		// Evaluate all arguments before rebinding any parameter. This matters for
		// loop back edges and permutations, even though SSA IDs are statically unique.
		values := make([]StatefulRuntimeValue, len(edge.Arguments))
		for i, id := range edge.Arguments {
			value, exists := env[id]
			if !exists || value.Type != next.Parameters[i].Type {
				return e.fail("invalid edge argument")
			}
			values[i] = value
		}
		for i, p := range next.Parameters {
			env[p.ID] = values[i]
		}
		block = next
	}
}
func (e *statefulExecutor) operation(op Operation, env map[ValueID]StatefulRuntimeValue) (StatefulExecutionOutcome, StatefulRuntimeValue) {
	args := make([]StatefulRuntimeValue, len(op.Operands))
	for i, id := range op.Operands {
		value, exists := env[id]
		if !exists {
			return e.fail("undefined operation operand")
		}
		args[i] = value
	}
	value := StatefulRuntimeValue{}
	if len(op.Results) == 1 {
		value.Type = op.Results[0].Type
	}
	switch op.Code {
	case OpConstInt:
		parsed, err := strconv.ParseUint(op.Attributes[0].Value, 10, 32)
		if err != nil {
			return e.fail("invalid integer constant")
		}
		value.Uint = uint32(parsed)
	case OpConstBool:
		value.Bool = op.Attributes[0].Value == "true"
	case OpConstUnit:
	case OpIntAdd:
		value.Uint = args[0].Uint + args[1].Uint
	case OpLess:
		value.Bool = args[0].Uint < args[1].Uint
	case OpEqual:
		value.Bool = args[0].Uint == args[1].Uint
	case OpDescriptorLen:
		value.Uint = args[0].Descriptor.Length
	case OpByteLoad, OpByteStore:
		descriptor, index := args[0].Descriptor, args[1].Uint
		if index >= descriptor.Length {
			return e.fail("byte index outside descriptor")
		}
		if descriptor.Base > math.MaxUint64-uint64(index) {
			return e.fail("byte address wraps")
		}
		address := descriptor.Base + uint64(index)
		prior, mapped := e.memory[address]
		if !mapped {
			return e.fail("byte address unmapped or uninitialized")
		}
		if op.Code == OpByteLoad {
			value.Uint = uint32(prior)
		} else {
			e.memory[address] = uint8(args[2].Uint)
		}
	case OpADTConstruct:
		value.Variant = op.Attributes[0].Value
		if len(args) == 1 {
			payload := cloneStatefulValue(args[0])
			value.Payload = &payload
		}
	case OpADTIsVariant:
		value.Bool = args[0].Variant == op.Attributes[0].Value
	case OpADTPayload:
		if args[0].Variant != op.Attributes[0].Value || args[0].Payload == nil {
			return e.fail("inactive ADT payload projection")
		}
		value = cloneStatefulValue(*args[0].Payload)
	case OpCall:
		name := op.Attributes[0].Value
		outcome, result := e.function(name, args)
		if outcome != StatefulReturned {
			return outcome, result
		}
		value = result
		e.calls = append(e.calls, StatefulCallResult{Function: name, Value: cloneStatefulValue(result)})
	default:
		return e.fail(fmt.Sprintf("unsupported operation %s", op.Code))
	}
	return StatefulReturned, value
}
