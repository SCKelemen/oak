package asm

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// Atomics under the verifier's sequential model (docs/spec/65-machine-memory.md
// section 7a). A cell is a span element reached by storage path; an atomic
// operation on it is a read of the element and a write into the span's log,
// on both sides:
//
//   - the Oak side lowers `atomic_load_*(v[i])` as the element's value,
//     `atomic_store_*(v[i], x)` as the write of x, `atomic_fetch_add_*` and
//     `atomic_exchange_*` as the write of `old + x` / `x` with the old
//     value as the result, and `atomic_compare_exchange_*` as the write of
//     the desired value under the guard `old = expected`, the old value as
//     the result (the strong CAS's observed value);
//   - the machine side executes the LSE forms (`cas*`, `ldadd*`, `swp*`,
//     `ldset*`, `ldclr*`, `ldeor*` and their `st*` variants) as the same
//     read and write, and the exclusive loop's `stxr`/`stlxr` as the store
//     with its status register zero: in the sequential model the exclusive
//     store succeeds, so the retry branch is decided and the loop runs once.
//     `clrex` is a no-op.
//
// The ordering is the checker's concern and the memory-model chapters'
// (65 §7a, 69); the values are these terms.

// atomicCell recognizes the cell argument `v[i]` of an atomic builtin: an
// element of a span parameter of cells, the index lowered at 32 bits.
func (lo *oakLowering) atomicCell(arg ast.Expression) (root string, contract spanContract, index *term, reason string, ok bool) {
	cell, isIndex := arg.(*ast.IndexExpression)
	if !isIndex || cell.Dot {
		return "", spanContract{}, nil, "an atomic on a cell that is not a span element", false
	}
	ident, isIdent := cell.Left.(*ast.Identifier)
	if !isIdent {
		return "", spanContract{}, nil, "an atomic on a cell that is not a span element", false
	}
	if _, shadowed := lo.locals[ident.Value]; shadowed {
		return "", spanContract{}, nil, fmt.Sprintf("an atomic on %s (a local, not a span parameter)", ident.Value), false
	}
	contract, isSpan := lo.spans[ident.Value]
	if !isSpan {
		return "", spanContract{}, nil, fmt.Sprintf("an atomic on %s (not a span parameter)", ident.Value), false
	}
	index, reason, ok = lo.lower(cell.Index, 32)
	if !ok {
		return "", spanContract{}, nil, reason, false
	}
	return lo.spanRoot(ident.Value), contract, index, "", true
}

// lowerAtomic lowers an atomic builtin call: its write into the span's log
// under the path condition, and the value it returns at width — the cell's
// value before the operation (nil for a store or a fence).
func (lo *oakLowering) lowerAtomic(spec semir.AtomicBuiltinSpec, call *ast.InvocationExpression, width int) (*term, string, bool) {
	if spec.Kind == semir.AtomicBuiltinFence {
		return nil, "", true
	}
	if len(call.Arguments) != int(spec.Arity) {
		return nil, "the atomic " + spec.Name + " with the wrong number of arguments", false
	}
	if spec.Kind == semir.AtomicBuiltinLoad {
		return lo.lower(call.Arguments[0], width)
	}
	root, contract, index, reason, ok := lo.atomicCell(call.Arguments[0])
	if !ok {
		return nil, reason, false
	}
	w := contract.elemWidth
	var old *term
	if spec.Kind != semir.AtomicBuiltinStore {
		element, _, reason, ok := lo.spanElementTerm(call.Arguments[0].(*ast.IndexExpression))
		if !ok {
			return nil, reason, false
		}
		old = element
	}
	guard := lo.path
	var value *term
	switch spec.Kind {
	case semir.AtomicBuiltinStore, semir.AtomicBuiltinExchange:
		v, reason, ok := lo.lower(call.Arguments[1], w)
		if !ok {
			return nil, reason, false
		}
		value = v
	case semir.AtomicBuiltinFetchAdd:
		v, reason, ok := lo.lower(call.Arguments[1], w)
		if !ok {
			return nil, reason, false
		}
		value = binaryTerm("add", old, v)
	case semir.AtomicBuiltinCompareExchange:
		expected, reason, ok := lo.lower(call.Arguments[1], w)
		if !ok {
			return nil, reason, false
		}
		desired, reason, ok := lo.lower(call.Arguments[2], w)
		if !ok {
			return nil, reason, false
		}
		value = desired
		equal := truncate(cmpTerm("eq", old, expected), 1)
		if guard == nil {
			guard = equal
		} else {
			guard = binaryTerm("and", guard, equal)
		}
	default:
		return nil, "the atomic " + spec.Name, false
	}
	lo.writes = appendWrite(lo.writes, root, index, truncate(value, w), guard)
	if old == nil {
		return nil, "", true
	}
	return adaptWidth(old, width), "", true
}

// cellAddress reads a register's term as a span element's address: the
// span base itself (element 0, or a constant offset's element) or an
// element address formed under the length guard (`add xE, xB, wI, uxtw #s`,
// elementBaseOf), as the checker's atomicAccess admits.
func (x *pathExecutor) cellAddress(base *term) (span string, index *term, elem int64, reason string, ok bool) {
	if param, offset, isSpan := spanBaseOf(base); isSpan {
		if _, isRecord := x.records[param]; isRecord {
			return "", nil, 0, "an atomic on a record argument", false
		}
		elem = x.spans[param]
		if elem == 0 || offset < 0 || offset%elem != 0 {
			return "", nil, 0, "an atomic at an address not aligned to an element", false
		}
		return param, constTerm(uint64(offset/elem), 32), elem, "", true
	}
	name, offset, idx, shift, isElement := elementBaseOf(base)
	if !isElement {
		return "", nil, 0, "an atomic through a register that is not a span base or an element address", false
	}
	if _, isRecord := x.records[name]; isRecord {
		return "", nil, 0, "an atomic on a record argument", false
	}
	elem = x.spans[name]
	if elem == 0 || int64(1)<<uint(shift) != elem || offset%elem != 0 {
		return "", nil, 0, "an atomic through an element address not aligned to an element", false
	}
	at := truncate(idx, 32)
	if extra := offset / elem; extra != 0 {
		at = binaryTerm("add", at, constTerm(uint64(extra), 32))
	}
	return name, at, elem, "", true
}

// atomicInstruction executes an exclusive store, an LSE atomic, or clrex
// through a span element (see the file comment). Reports whether the
// instruction was one of them.
func (x *pathExecutor) atomicInstruction(instr Instruction, state *symbolicState) (handled bool, reason string, ok bool) {
	name := instr.Mnemonic
	if name == "clrex" {
		return true, "", true
	}
	if !isAtomic(name) && !isExclusiveStore(name) {
		return false, "", false
	}
	if len(x.loopStack) > 0 {
		return true, "an atomic in a data-dependent loop body", false
	}
	mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory)
	if !isMem || mem.Base.Class != ClassX || mem.Index != nil || mem.Mode != MemOffset || mem.Offset != 0 {
		return true, "an atomic whose address is not a bare span element", false
	}
	regs := registerOperands(instr.Operands[:len(instr.Operands)-1])
	if len(regs) != 2 && !(len(regs) == 1 && strings.HasPrefix(atomicBase(name), "st")) {
		return true, "an atomic pair (" + name + ")", false
	}
	for _, reg := range regs {
		if reg.Class == ClassV {
			return true, "a vector-register atomic", false
		}
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound {
		return true, "an atomic through a register that is not a span base", false
	}
	span, index, elem, reason, ok := x.cellAddress(base)
	if !ok {
		return true, reason, false
	}
	if size := memorySize(name, regs[len(regs)-1].Class); size != elem {
		return true, fmt.Sprintf("a %d-byte atomic over %d-byte elements", size, elem), false
	}
	w := int(elem) * 8
	old := x.elementIn(state, span, index, w)
	if isExclusiveStore(name) {
		// stxr Ws, Wt, [Xn]: the store of Wt, the status Ws zero.
		value, okValue := state.read(regs[1])
		if !okValue {
			return true, "unbound register read", false
		}
		state.writes = appendWrite(state.writes, span, index, truncate(value, w), nil)
		state.write(regs[0], constTerm(0, widthOf(regs[0].Class)))
		return true, "", true
	}
	source, okSource := state.read(regs[0])
	if !okSource {
		return true, "unbound register read", false
	}
	source = truncate(source, w)
	base_ := atomicBase(name)
	switch base_ {
	case "cas":
		// cas Ws, Wt, [Xn]: Wt stored when the cell held Ws; Ws receives
		// the value observed either way.
		desired, okDesired := state.read(regs[1])
		if !okDesired {
			return true, "unbound register read", false
		}
		guard := truncate(cmpTerm("eq", old, source), 1)
		state.writes = appendWrite(state.writes, span, index, truncate(desired, w), guard)
		state.write(regs[0], zeroExtend(old, widthOf(regs[0].Class)))
		return true, "", true
	}
	var value *term
	switch strings.TrimPrefix(strings.TrimPrefix(base_, "ld"), "st") {
	case "add":
		value = binaryTerm("add", old, source)
	case "set":
		value = binaryTerm("or", old, source)
	case "clr":
		value = binaryTerm("and", old, binaryTerm("xor", source, constTerm(mask(w), w)))
	case "eor":
		value = binaryTerm("xor", old, source)
	default:
		if base_ == "swp" {
			value = source
		} else {
			return true, "the atomic " + name + " (a minimum or maximum, not modeled)", false
		}
	}
	state.writes = appendWrite(state.writes, span, index, truncate(value, w), nil)
	if !strings.HasPrefix(base_, "st") {
		state.write(regs[1], zeroExtend(old, widthOf(regs[1].Class)))
	}
	return true, "", true
}
