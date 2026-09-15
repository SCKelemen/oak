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

// spanWrite is one store to a span parameter along a path — or, with
// memory set, a loop memory marker: from here the span's contents are the
// unknown memory `loop<K>.<span>` (the span as some iteration of loop K
// sees it, and as the loop leaves it), whose element at an index is a
// select over that name. Both sides place the marker at the same loop,
// and the coupling proof shows the loops' iterations store alike
// (verifyLoops), so the two unknown memories are the same memory.
type spanWrite struct {
	index  *term  // 32-bit element index
	value  *term  // at the element width
	guard  *term  // 1-bit condition under which the store happens; nil: always
	memory string // a loop memory marker's name, "" for a store
}

// loopMemoryName is the unknown memory of a span across loop K.
func loopMemoryName(loop int, span string) string { return fmt.Sprintf("loop%d.%s", loop, span) }

// appendMarker records that from here the span's contents are the loop's
// unknown memory.
func appendMarker(log map[string][]*spanWrite, span string, loop int) map[string][]*spanWrite {
	if log == nil {
		log = map[string][]*spanWrite{}
	}
	log[span] = append(log[span][:len(log[span]):len(log[span])], &spanWrite{memory: loopMemoryName(loop, span)})
	return log
}

// pathEffects is what a path through the asm body leaves behind besides
// its result: the package cells and the span memories it wrote.
type pathEffects struct {
	cells  map[string]*term
	writes map[string][]*spanWrite
	// trap is the 1-bit condition under which the machine path traps
	// (brk): nil when no path from here does. The equivalence holds on
	// the inputs where the machine does not trap — where Oak traps too,
	// on the same guard — so the decision conjoins its negation to the
	// input domain (oakLowering.domainCondition).
	trap *term
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
	var form *linearForm
	if len(log) > 0 {
		form = index.linearAt(32)
	}
	for _, w := range log {
		if w.memory != "" {
			// A loop memory marker: the element is the unknown memory's,
			// under the marker's guard when it has one (an inner loop
			// reached on some of the enclosing body's paths).
			at := selectTerm(w.memory, index, base.width)
			if w.guard != nil {
				at = iteTerm(truncate(w.guard, 1), at, value)
			}
			value = at
			continue
		}
		// Two indices in linear normal form over the same unknowns are
		// equal or unequal by their constants alone — the arena's
		// `base + k` addressing — which spares the diagrams an equality
		// over the index bits for every write met by a read.
		var known, equal bool
		if index.kind == termConst && w.index.kind == termConst {
			// Two constants (a witness run): compared outright.
			known, equal = true, index.value&mask(32) == w.index.value&mask(32)
		} else {
			known, equal = indexRelation(form, w.index)
		}
		if known && !equal {
			continue
		}
		var hit *term
		if !known {
			hit = truncate(cmpTerm("eq", index, w.index), 1)
		}
		if w.guard != nil {
			if hit == nil {
				hit = truncate(w.guard, 1)
			} else {
				hit = binaryTerm("and", truncate(w.guard, 1), hit)
			}
		}
		if hit == nil {
			value = w.value
			continue
		}
		value = iteTerm(hit, w.value, value)
	}
	return value
}

// indexRelation decides, syntactically, whether an index (in linear normal
// form at 32 bits, nil when it has none) equals another: both linear over
// the same unknowns with the same coefficients, they are equal exactly
// when their constants agree, modulo 2^32; otherwise unknown.
func indexRelation(form *linearForm, other *term) (known, equal bool) {
	if form == nil {
		return false, false
	}
	lb := other.linearAt(32)
	if lb == nil || len(form.coeffs) != len(lb.coeffs) {
		return false, false
	}
	for name, c := range form.coeffs {
		if lb.coeffs[name] != c {
			return false, false
		}
	}
	return true, form.constant == lb.constant
}

// guardWrites conjoins cond onto the guard of every write in the slice.
func guardWrites(writes []*spanWrite, cond *term) []*spanWrite {
	out := make([]*spanWrite, 0, len(writes))
	for _, w := range writes {
		guard := cond
		if w.guard != nil {
			guard = binaryTerm("and", truncate(w.guard, 1), cond)
		}
		out = append(out, &spanWrite{index: w.index, value: w.value, guard: guard, memory: w.memory})
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
	return &pathEffects{cells: x.mergeCells(cond, takenCells, fallCells), writes: mergeWrites(cond, takenWrites, fallWrites), trap: mergeTrap(cond, taken, fallThrough)}
}

// mergeTrap is the trap condition of a fork: the taken side's under cond,
// the fall-through's otherwise; nil when neither side traps.
func mergeTrap(cond *term, taken, fallThrough *pathEffects) *term {
	var takenTrap, fallTrap *term
	if taken != nil {
		takenTrap = taken.trap
	}
	if fallThrough != nil {
		fallTrap = fallThrough.trap
	}
	if takenTrap == nil && fallTrap == nil {
		return nil
	}
	if takenTrap == nil {
		takenTrap = constTerm(0, 1)
	}
	if fallTrap == nil {
		fallTrap = constTerm(0, 1)
	}
	return iteTerm(truncate(cond, 1), takenTrap, fallTrap)
}

// withTrap is effects with the trap condition set: the surviving side of a
// fork whose other side trapped keeps its cells and writes and records
// where the machine trapped.
func withTrap(effects *pathEffects, trap *term) *pathEffects {
	if effects == nil {
		return &pathEffects{trap: trap}
	}
	out := *effects
	out.trap = trap
	return &out
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
	if handled, reason, ok := x.recordSpanStore(instr, mem, base, state); handled {
		return true, reason, ok
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
		if derived, at, isDerived := spanAddressOf(base, elem); isDerived && elem > 0 {
			// A derived span's base (asm/derived_spans.go): the root's
			// index is the sum, a scaled index in the addressing mode added.
			param, index, offset, shift = derived, at, 0, log2(elem)
			if mem.Index != nil {
				if int64(1)<<uint(mem.Shift) != elem {
					return true, "an indexed store whose scale is not the element size", false
				}
				further, ok := state.read(*mem.Index)
				if !ok {
					return true, "unbound register read", false
				}
				index = addIndex(index, truncate(further, 32))
				mem.Index = nil
			}
			if index == nil {
				index = constTerm(0, 32)
			}
		}
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
	if !isReg {
		return true, "a store to a span from an operand that is not a register", false
	}
	// A vector register's store (`str qN` / `str dN`) writes its bytes as
	// whole elements: one write per lane, at consecutive indices — the
	// native lowering's `simd.store` (nativegen/simd.go), the Oak side's
	// simdStore (asm/verify_simd.go). A scalar float's store (`str sN`,
	// `str dN`, `str hN`) is the one-lane case: the register's low lane at
	// the element's width — `ys[i] = x` over `[*]f32` (nativegen's float
	// span store), decided up to the IEEE operations like every float
	// value (docs/spec/94-assembler.md §8).
	vector := src.Class == ClassV
	if vector && (src.Lane >= 0 || instr.Mnemonic != "str" || (src.VecBytes() != 16 && src.VecBytes() != 8 && src.VecBytes() != 4 && src.VecBytes() != 2)) {
		return true, "a vector-register store to a span through the " + src.Vec + " view", false
	}
	if mem.Mode != MemOffset {
		return true, "a span base moved by pre/post-index", false
	}
	if vector {
		if int64(src.VecBytes())%elem != 0 {
			return true, fmt.Sprintf("a %d-byte vector store over %d-byte elements", src.VecBytes(), elem), false
		}
	} else if size := memorySize(instr.Mnemonic, src.Class); size != elem {
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
	if vector {
		value, okVec := state.readVec(src.Num)
		if !okVec {
			return true, "unbound vector register read", false
		}
		bits := int(elem) * 8
		lanes := value.lanesAt(bits)[:int64(src.VecBytes())/elem]
		for k, lane := range lanes {
			at := index
			if k > 0 {
				at = binaryTerm("add", index, constTerm(uint64(k), 32))
			}
			state.writes = appendWrite(state.writes, param, at, truncate(lane, bits), nil)
		}
		return true, "", true
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
	index, reason, ok := lo.lower(s.Target.Index, 32)
	if !ok {
		return reason, false
	}
	value, reason, ok := lo.lower(s.Value, contract.elemWidth)
	if !ok {
		return reason, false
	}
	root := lo.spanRoot(name)
	if lo.concrete != nil {
		// Past the span's own length: Oak traps on this input (noted by
		// the witness run under the path).
		lo.addTrap(cmpTerm("hs", index, lo.witnessBound(name)))
		if lo.witnessTrapped {
			return fmt.Sprintf("an index past len(%s) on this input", name), false
		}
	}
	index = lo.spanIndex(name, index) // a derived span: start + i in the root
	lo.writes = appendWrite(lo.writes, root, index, truncate(value, contract.elemWidth), lo.path)
	return "", true
}

// isSpanLength reports a term that is the caller's span length: the
// parameter `len(v)` in a symbolic run, its concrete value in a witness
// run (where the length register holds the input's constant).
func (x *pathExecutor) isSpanLength(length *term, span string) bool {
	if x.concrete {
		value, known := x.env[spanLenName(span)]
		return known && length.kind == termConst && length.value&mask(32) == value&mask(32)
	}
	return isParamNamed(length, spanLenName(span))
}

// isParamNamed reports a term that is the parameter name at any width:
// the node itself, or its zero-extension by a mask (the width adapters
// copy a parameter node at the use width).
func isParamNamed(t *term, name string) bool {
	switch t.kind {
	case termParam:
		return t.name == name
	case termBinary:
		return t.op == "and" && t.right.kind == termConst && isParamNamed(t.left, name)
	}
	return false
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
		var width int
		if leafWidth, isLeaf := lowering.recordLeafWidth(name); isLeaf {
			// A record span's leaf memory (`v.f`): the leaf's width.
			width = leafWidth
		} else {
			contract, isSpan := lowering.spans[name]
			if !isSpan {
				return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (a store through %s, which the Oak signature does not declare as a span) — trusted per docs/spec/94-assembler.md §5", fn.Name, name)}
			}
			width = contract.elemWidth
			if elem := exec.spans[name]; int(elem)*8 != width {
				return Verdict{Kind: VerdictTrusted, Message: fmt.Sprintf("asm unit %s: not verified (the span %s has %d-byte elements in the contract and %d-bit ones in the Oak signature) — trusted per docs/spec/94-assembler.md §5", fn.Name, name, elem, width)}
			}
		}
		lowering.fresh[spanIndexName(name)] = 32
		at := paramTerm(spanIndexName(name), 32)
		entry := selectTerm(name, at, width)
		// Two logs of the same unconditional writes at the same indices in
		// the same order leave the same memory exactly when each pair of
		// values agrees: a vector store's sixteen lanes decide as sixteen
		// small equalities rather than one sixteen-way conditional at a
		// symbolic index (Oak.Simd.store_lane). Otherwise the memories are
		// compared at the fresh index.
		// The fast path only proves: a pair that fails to prove — values
		// that differ where a later write overrides them, or writes under
		// complementary guards logged in opposite orders — leaves the
		// decision to the memories themselves, never refutes on its own.
		if pairs, aligned := alignedWrites(exec.writes[name], lowering.writes[name], width); aligned {
			decided := true
			for _, pair := range pairs {
				if verdict := decideEqual(fn, lowering, pair.asm, pair.oak, pair.width, ""); verdict.Kind != VerdictProven {
					decided = false
					break
				}
			}
			if decided {
				continue
			}
		}
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

// writePair is one equality the aligned fast path decides: two values at
// the element width, or two guards at one bit.
type writePair struct {
	asm, oak *term
	width    int
}

// alignedWrites pairs the values of two write logs that are the same
// sequence of writes at the same indices (each index pair equal in linear
// normal form): the values, and — for writes guarded on both sides, as a
// store under a conditional is — the guards, decided as one-bit terms.
// False when the logs differ in length, a write is guarded on one side
// only, or an index pair is not known equal.
func alignedWrites(asm, oak []*spanWrite, width int) ([]writePair, bool) {
	if len(asm) == 0 || len(asm) != len(oak) {
		return nil, false
	}
	var pairs []writePair
	for i := range asm {
		if (asm[i].guard == nil) != (oak[i].guard == nil) || asm[i].memory != "" || oak[i].memory != "" {
			return nil, false
		}
		known, equal := indexRelation(asm[i].index.linearAt(32), oak[i].index)
		if !known || !equal {
			return nil, false
		}
		if asm[i].guard != nil {
			// Guarded on both sides: the guards must agree, and the values
			// where the guard holds (elsewhere the store does not happen).
			ga, go_ := truncate(asm[i].guard, 1), truncate(oak[i].guard, 1)
			pairs = append(pairs, writePair{asm: ga, oak: go_, width: 1})
			zero := constTerm(0, width)
			pairs = append(pairs, writePair{asm: iteTerm(ga, asm[i].value, zero), oak: iteTerm(go_, oak[i].value, zero), width: width})
			continue
		}
		pairs = append(pairs, writePair{asm: asm[i].value, oak: oak[i].value, width: width})
	}
	return pairs, true
}

// decideEffects decides the package cells and then the span memories
// either side writes, after the result's proven verdict when there is one.
func decideEffects(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	writesCells := len(exec.cells) > 0 || len(lowering.writtenCells()) > 0
	writesSpans := len(exec.writes) > 0 || len(lowering.writes) > 0
	if !writesCells && !writesSpans && result == nil {
		// A unit body with no effect on either side — an assert over a
		// call, a body whose stores the model tracks are none — leaves the
		// entry state as it is on both sides, so the sides agree
		// (docs/spec/94-assembler.md §8, unit bodies without effects;
		// Oak.UnitBodies: an empty effect log is the identity).
		return Verdict{Kind: VerdictProven, Message: fmt.Sprintf("asm unit %s: proven equal to its Oak body (a unit body that writes no package state and no span memory on either side)", fn.Name)}
	}
	if writesCells {
		verdict := decideCells(fn, lowering, exec, result)
		if verdict.Kind != VerdictProven || !writesSpans {
			return verdict
		}
		result = &verdict
	}
	return decideSpans(fn, lowering, exec, result)
}
