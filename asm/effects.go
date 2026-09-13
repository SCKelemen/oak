package asm

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// Memory effects through span parameters (docs/spec/94-assembler.md §9,
// the twenty-eighth increment). A function's stores through a span
// parameter are its observable effect besides the result and the package
// cells; the verdict compares them as it compares a result.
//
// Both sides keep, per span parameter, a write log: the stores made so
// far along the path, each an index term at 32 bits, a value term at the
// element width, and a guard (nil: unconditional) — the path condition
// the Oak side lowers under, or the fork condition the asm side's paths
// meet under when they rejoin. A read consults the log newest-first and
// falls through to the entry memory (the select or the element parameter),
// so a read after a write sees the write on both sides alike. The final
// memory of a span is compared at a fresh symbolic index — equal at every
// index is equal memories — through the same decision as a result:
// witnesses, the linear form, and the bit-level diagrams under the reads'
// functional consistency.
//
// The seam checker has already proven every store in bounds under a
// dominating length guard, so the verifier's only question is which
// element a store reaches and what it stores. A store inside a
// data-dependent loop body, into a by-reference record argument, of a
// register pair, or of a vector register is outside the subset and leaves
// the function trusted with the reason.

// spanWrite is one store to a span parameter along a path.
type spanWrite struct {
	index *term // 32-bit element index
	value *term // at the element width
	guard *term // 1-bit condition under which the store happens; nil: always
}

// pathEffects is what a path through the asm body leaves behind besides
// its result: the package cells and the span memories it wrote.
type pathEffects struct {
	cells  map[string]*term
	writes map[string][]*spanWrite
}

func (s *symbolicState) effects() *pathEffects {
	return &pathEffects{cells: s.globals, writes: s.writes}
}

// appendWrite records a store to span at index of value under guard.
func appendWrite(log map[string][]*spanWrite, span string, index, value, guard *term) map[string][]*spanWrite {
	if log == nil {
		log = map[string][]*spanWrite{}
	}
	log[span] = append(log[span][:len(log[span]):len(log[span])], &spanWrite{index: truncate(index, 32), value: value, guard: guard})
	return log
}

// cloneWrites copies a write log for a forked path: the entries are
// shared (never mutated), the slices are not.
func cloneWrites(log map[string][]*spanWrite) map[string][]*spanWrite {
	if len(log) == 0 {
		return nil
	}
	out := make(map[string][]*spanWrite, len(log))
	for span, writes := range log {
		out[span] = writes[:len(writes):len(writes)]
	}
	return out
}

// memoryAt is the element of span at index after the writes in log, over
// the entry memory base: the newest write whose guard holds at an equal
// index, else the next older, else the entry value. A constant index
// against a constant write index folds, so straight-line code at literal
// indices costs no conditional.
func memoryAt(log []*spanWrite, index, base *term) *term {
	value := base
	index = truncate(index, 32)
	for _, w := range log {
		hit := truncate(cmpTerm("eq", index, w.index), 1)
		if w.guard != nil {
			hit = binaryTerm("and", truncate(w.guard, 1), hit)
		}
		value = iteTerm(hit, w.value, value)
	}
	return value
}

// guardWrites conjoins cond onto the guard of every write in the slice.
func guardWrites(writes []*spanWrite, cond *term) []*spanWrite {
	out := make([]*spanWrite, 0, len(writes))
	for _, w := range writes {
		guard := cond
		if w.guard != nil {
			guard = binaryTerm("and", truncate(w.guard, 1), cond)
		}
		out = append(out, &spanWrite{index: w.index, value: w.value, guard: guard})
	}
	return out
}

// mergeWrites joins the write logs of a fork's two paths: the writes both
// made before the fork (the shared prefix) stay as they are, the taken
// path's own writes run under cond and the fall-through path's under its
// negation. The two remainders are exclusive, so their order in the merged
// log is immaterial.
func mergeWrites(cond *term, taken, fallThrough map[string][]*spanWrite) map[string][]*spanWrite {
	if len(taken) == 0 && len(fallThrough) == 0 {
		return nil
	}
	cond = truncate(cond, 1)
	merged := map[string][]*spanWrite{}
	for span := range taken {
		merged[span] = nil
	}
	for span := range fallThrough {
		merged[span] = nil
	}
	for span := range merged {
		t, f := taken[span], fallThrough[span]
		shared := 0
		for shared < len(t) && shared < len(f) && t[shared] == f[shared] {
			shared++
		}
		log := append([]*spanWrite{}, t[:shared]...)
		log = append(log, guardWrites(t[shared:], cond)...)
		log = append(log, guardWrites(f[shared:], notTerm(cond))...)
		merged[span] = log
	}
	return merged
}

// mergeEffects joins the effects of a fork's two paths.
func (x *pathExecutor) mergeEffects(cond *term, taken, fallThrough *pathEffects) *pathEffects {
	var takenCells, fallCells map[string]*term
	var takenWrites, fallWrites map[string][]*spanWrite
	if taken != nil {
		takenCells, takenWrites = taken.cells, taken.writes
	}
	if fallThrough != nil {
		fallCells, fallWrites = fallThrough.cells, fallThrough.writes
	}
	return &pathEffects{cells: x.mergeCells(cond, takenCells, fallCells), writes: mergeWrites(cond, takenWrites, fallWrites)}
}

// elementIn is the span element at an index term as the path sees it:
// the newest store on the path at that index, else the entry memory
// (element), which in a concrete run is the witness memory's value.
func (x *pathExecutor) elementIn(state *symbolicState, span string, index *term, width int) *term {
	return memoryAt(state.writes[span], index, x.element(span, index, width))
}

// spanStore executes a store through a span parameter's base: the
// element at the address takes the stored register's value at the element
// width. Reports whether the instruction was a store through a span.
func (x *pathExecutor) spanStore(instr Instruction, state *symbolicState) (handled bool, reason string, ok bool) {
	if !isStoreMnemonic(instr.Mnemonic) || len(instr.Operands) < 2 {
		return false, "", false
	}
	mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory)
	if !isMem || mem.Base.Class != ClassX {
		return false, "", false
	}
	base, bound := state.regs[mem.Base.Num]
	if !bound {
		return false, "", false
	}
	param, baseOffset, isSpan := spanBaseOf(base)
	var index *term
	if isSpan {
		if _, isRecord := x.records[param]; isRecord {
			return true, "a store into a record argument", false
		}
	} else {
		var offset int64
		var shift int
		name, off, idx, sh, isElement := elementBaseOf(base)
		if !isElement {
			return false, "", false
		}
		param, offset, index, shift = name, off, idx, sh
		elem := x.spans[param]
		if elem == 0 || int64(1)<<uint(shift) != elem || offset%elem != 0 {
			return true, "a store through an element address not aligned to an element", false
		}
		baseOffset = offset
	}
	elem, known := x.spans[param]
	if !known || elem == 0 {
		return false, "", false
	}
	if len(instr.Operands) != 2 {
		return true, "a pair store to a span", false
	}
	src, isReg := instr.Operands[0].(Register)
	if !isReg || src.Class == ClassV {
		return true, "a vector-register store to a span", false
	}
	if len(x.loopStack) > 0 {
		return true, "a span store in a data-dependent loop body", false
	}
	if mem.Mode != MemOffset {
		return true, "a span base moved by pre/post-index", false
	}
	if size := memorySize(instr.Mnemonic, src.Class); size != elem {
		return true, fmt.Sprintf("a %d-byte store over %d-byte elements", size, elem), false
	}
	if baseOffset%elem != 0 || mem.Offset%elem != 0 {
		return true, "a store not aligned to an element", false
	}
	extra := baseOffset/elem + mem.Offset/elem
	switch {
	case index != nil:
		// An element address in the base (add xE, xB, wI, uxtw #s).
		if mem.Index != nil {
			return true, "an indexed store through an element address", false
		}
		index = truncate(index, 32)
	case mem.Index != nil:
		// [base, wI, uxtw #s]: element wI.
		if int64(1)<<uint(mem.Shift) != elem {
			return true, "an indexed store whose scale is not the element size", false
		}
		idx, okIndex := state.read(*mem.Index)
		if !okIndex {
			return true, "unbound register read", false
		}
		index = truncate(idx, 32)
	default:
		if mem.Offset < 0 {
			return true, "a store below the span base", false
		}
		index = constTerm(0, 32)
	}
	if extra != 0 {
		index = binaryTerm("add", index, constTerm(uint64(extra), 32))
	}
	value, okValue := state.read(src)
	if !okValue {
		return true, "unbound register read", false
	}
	state.writes = appendWrite(state.writes, param, index, truncate(value, int(elem)*8), nil)
	return true, "", true
}

// --- the Oak side ---------------------------------------------------------

// spanAssignment recognizes `v[e] = value` over a span parameter.
func (lo *oakLowering) spanAssignment(s *ast.IndexAssignmentStatement) (name string, contract spanContract, ok bool) {
	if s.Target == nil || s.Target.Dot {
		return "", spanContract{}, false
	}
	ident, isIdent := s.Target.Left.(*ast.Identifier)
	if !isIdent {
		return "", spanContract{}, false
	}
	if _, shadowed := lo.locals[ident.Value]; shadowed {
		return "", spanContract{}, false
	}
	contract, isSpan := lo.spans[ident.Value]
	return ident.Value, contract, isSpan
}

// assignSpanElement lowers `v[e] = value` over a span parameter as a write
// to the span's log under the path condition. The bound is the checker's
// (the store is dominated by a length guard); the verifier records which
// element takes which value.
func (lo *oakLowering) assignSpanElement(name string, contract spanContract, s *ast.IndexAssignmentStatement) (string, bool) {
	if len(lo.loopStack) > 0 {
		return "a span store in a data-dependent loop body", false
	}
	index, reason, ok := lo.lower(s.Target.Index, 32)
	if !ok {
		return reason, false
	}
	value, reason, ok := lo.lower(s.Value, contract.elemWidth)
	if !ok {
		return reason, false
	}
	if lo.concrete != nil && index.kind == termConst {
		if length, known := lo.concrete[spanLenName(name)]; known && index.value >= length {
			return fmt.Sprintf("an index past len(%s) on this input", name), false
		}
	}
	lo.writes = appendWrite(lo.writes, name, index, truncate(value, contract.elemWidth), lo.path)
	return "", true
}

// --- the decision ----------------------------------------------------------

// spanIndexName is the fresh index at which a span's final memories are
// compared: `v[?]` reads as "an element of v".
func spanIndexName(span string) string { return span + "[?]" }

// decideSpans decides, for every span parameter either side stores
// through, that the two sides leave the same memory: the final element at
// a fresh symbolic index, over the entry memory, is compared as a result
// is. A side that never stores through a span leaves its entry memory.
// result is the proven verdict so far (the result, the cells) when there
// is one; the proof's message names the spans.
func decideSpans(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	names := map[string]bool{}
	for name := range exec.writes {
		names[name] = true
	}
	for name := range lowering.writes {
		names[name] = true
	}
	if len(names) == 0 {
		if result != nil {
			return *result
		}
		return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (no integer result) — trusted per docs/spec/94-assembler.md §5", fn.Name)}
	}
	sorted := make([]string, 0, len(names))
	for name := range names {
		sorted = append(sorted, name)
	}
	sort.Strings(sorted)
	for _, name := range sorted {
		contract, isSpan := lowering.spans[name]
		if !isSpan {
			return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (a store through %s, which the Oak signature does not declare as a span) — trusted per docs/spec/94-assembler.md §5", fn.Name, name)}
		}
		width := contract.elemWidth
		if elem := exec.spans[name]; int(elem)*8 != width {
			return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the span %s has %d-byte elements in the contract and %d-bit ones in the Oak signature) — trusted per docs/spec/94-assembler.md §5", fn.Name, name, elem, width)}
		}
		lowering.fresh[spanIndexName(name)] = 32
		at := paramTerm(spanIndexName(name), 32)
		entry := selectTerm(name, at, width)
		asmMemory := memoryAt(exec.writes[name], at, entry)
		oakMemory := memoryAt(lowering.writes[name], at, entry)
		verdict := decideEqual(fn, lowering, asmMemory, oakMemory, width, "")
		if verdict.Kind != VerdictProven {
			verdict.Message = strings.Replace(verdict.Message, "asm unit "+fn.Name, fmt.Sprintf("asm unit %s (the span %s)", fn.Name, name), 1)
			return verdict
		}
	}
	spans := "the span memory it writes (" + strings.Join(sorted, ", ") + ")"
	if result != nil {
		return Verdict{Kind: VerdictProven, Message: result.Message + " and " + spans}
	}
	return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body in %s", fn.Name, spans)}
}

// decideEffects decides the package cells and then the span memories
// either side writes, after the result's proven verdict when there is one.
func decideEffects(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	writesCells := len(exec.cells) > 0 || len(lowering.writtenCells()) > 0
	writesSpans := len(exec.writes) > 0 || len(lowering.writes) > 0
	if writesCells {
		verdict := decideCells(fn, lowering, exec, result)
		if verdict.Kind != VerdictProven || !writesSpans {
			return verdict
		}
		result = &verdict
	}
	return decideSpans(fn, lowering, exec, result)
}
