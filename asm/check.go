package asm

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// Check enforces the seams of one asm function against its Oak declaration
// (docs/spec/94-assembler.md §2–§4). symbols is the set of Oak-visible
// function names a `b`/`bl` may target. Every finding is a hard error; the
// checker fails closed on anything it cannot prove.
//
// What is checked, linearly over the block:
//   - signature identity with the Oak declaration (structural);
//   - every parameter bound to its AAPCS64 contract register at the
//     parameter's width class, and nothing else bound;
//   - operand forms and width discipline per the instruction table;
//   - reads only of bound, written, sp, or zero registers (no uninitialized
//     reads); writes only to bound registers, the result register, or
//     declared clobbers; callee-saved registers refused in v1;
//   - flags consumers dominated by a producer (labels and calls invalidate);
//   - memory only through the declared sp frame, offsets bounds-checked
//     against `frame N` with the static sp displacement tracked through
//     pre/post-index and sp arithmetic, consistent at every label;
//   - `align N` regions whose instruction bytes fit N (every AArch64
//     instruction is 4 bytes, so the extent is exact);
//   - mrs/msr/eret only under the unit's `system` capability;
//   - the result register written before every `ret`; no `ret` from a
//     `never` function; no fall-through past the end.
func Check(fn *Function, decl *ast.FunctionStatement, symbols map[string]bool) []string {
	// Guard facts across labels are a dataflow fixpoint: each pass assumes
	// a guard state at every label, records the meet of the states that
	// actually arrive there (by fall-through and by every branch, forward
	// or backward), and the passes repeat until the assumptions are exactly
	// the arrivals. The first pass assumes everything (top); facts only
	// shrink, so the iteration terminates. Only the stable pass reports.
	var labelIn map[string]*guardState
	for pass := 0; pass < maxGuardPasses; pass++ {
		c := runPass(fn, decl, symbols, labelIn, false)
		if len(c.errors) != 0 && c.labelArrive == nil {
			return c.errors // signature errors: nothing to iterate
		}
		if labelIn != nil && guardStatesEqual(labelIn, c.labelArrive) {
			return c.errors
		}
		labelIn = c.labelArrive
	}
	// Past the cap: the conservative pass forgets every guard at every
	// label (a sound assumption, the pre-fixpoint behavior).
	return runPass(fn, decl, symbols, nil, true).errors
}

// maxGuardPasses caps the fixpoint iteration.
const maxGuardPasses = 16

func runPass(fn *Function, decl *ast.FunctionStatement, symbols map[string]bool, labelIn map[string]*guardState, forgetAtLabels bool) *checker {
	c := &checker{fn: fn, symbols: symbols, labelIn: labelIn, forgetAtLabels: forgetAtLabels}
	c.checkSignature(decl)
	if len(c.errors) != 0 {
		return c
	}
	c.labelArrive = map[string]*guardState{}
	c.bindContract()
	c.declareClobbers()
	c.walk()
	return c
}

// guardState is the guard knowledge at a program point: per span base
// register the proven minimum length, per index register its bound, per
// register the frame address it holds.
type guardState struct {
	mins  map[int]int64
	idx   map[int]idxFact
	frame map[int]int64
}

func newGuardState() *guardState {
	return &guardState{mins: map[int]int64{}, idx: map[int]idxFact{}, frame: map[int]int64{}}
}

func (c *checker) guardSnapshot() *guardState {
	gs := newGuardState()
	for base, fact := range c.spans {
		if fact.hasMin {
			gs.mins[base] = fact.minLen
		}
	}
	for reg, fact := range c.idxFacts {
		gs.idx[reg] = fact
	}
	for reg, addr := range c.frameAddrs {
		gs.frame[reg] = addr
	}
	return gs
}

// applyGuards installs a label's guard state: exactly the facts it holds,
// on the spans that still exist.
func (c *checker) applyGuards(gs *guardState) {
	for base, fact := range c.spans {
		minLen, has := gs.mins[base]
		fact.hasMin = has
		fact.minLen = minLen
	}
	c.idxFacts = map[int]idxFact{}
	for reg, fact := range gs.idx {
		c.idxFacts[reg] = fact
	}
	c.frameAddrs = map[int]int64{}
	for reg, addr := range gs.frame {
		c.frameAddrs[reg] = addr
	}
	c.pendingCmp = cmpFact{}
}

// meetGuards is the intersection of two states: a length bound holds after
// a merge only at the smaller of the two proven minimums
// (Oak.Assembler.meet_sound), an index fact or a frame address only when
// both sides agree.
func meetGuards(a, b *guardState) *guardState {
	if a == nil {
		return b
	}
	if b == nil {
		return a
	}
	out := newGuardState()
	for reg, addrA := range a.frame {
		if addrB, ok := b.frame[reg]; ok && addrA == addrB {
			out.frame[reg] = addrA
		}
	}
	for base, minA := range a.mins {
		if minB, ok := b.mins[base]; ok {
			out.mins[base] = min(minA, minB)
		}
	}
	for reg, factA := range a.idx {
		if factB, ok := b.idx[reg]; ok && factA == factB {
			out.idx[reg] = factA
		}
	}
	return out
}

// arrive records a state reaching a label.
func (c *checker) arrive(label string) {
	if c.labelArrive == nil {
		return
	}
	c.labelArrive[label] = meetGuards(c.labelArrive[label], c.guardSnapshot())
}

func guardStatesEqual(a, b map[string]*guardState) bool {
	if len(a) != len(b) {
		return false
	}
	for name, ga := range a {
		gb, ok := b[name]
		if !ok || len(ga.mins) != len(gb.mins) || len(ga.idx) != len(gb.idx) || len(ga.frame) != len(gb.frame) {
			return false
		}
		for reg, addr := range ga.frame {
			if gb.frame[reg] != addr {
				return false
			}
		}
		for base, m := range ga.mins {
			if gb.mins[base] != m {
				return false
			}
		}
		for reg, f := range ga.idx {
			if gb.idx[reg] != f {
				return false
			}
		}
	}
	return true
}

type checker struct {
	fn      *Function
	symbols map[string]bool
	errors  []string

	// contract
	paramClass    map[string]RegClass // parameter -> width class
	paramRegister map[string]int      // parameter -> contract register number
	paramView     map[string]string   // parameter -> "s"/"d" for f32/f64, "" otherwise
	resultClass   RegClass
	hasResult     bool
	never         bool

	// authority
	bound     map[int]bool // register numbers bound to parameters
	clobbered map[int]bool // declared clobbers (general file)
	clobberV  map[int]bool // declared vector clobbers (v and z)
	clobberP  map[int]bool // declared predicate clobbers (p and pn)
	// The streaming-mode and ZA state (asm/isa_sme.go): tracked along the
	// block from smstart/smstop; vZeroed marks that a mode switch zeroed
	// the vector registers since entry, so a bound vector is gone.
	sm, za  bool
	vZeroed bool
	// spans: base register number -> the span it points at (typed pointer
	// parameters); guard facts live here and die with any write to the
	// base or length register, any label, and any call.
	spans      map[int]*spanFact
	spanParams map[string]spanParam
	pendingCmp cmpFact
	// idxFacts: index register -> the bound a dominating guard proved it
	// below (`cmp wI, wL` / `cmp wI, #K` then `b.hs <exit>`); they die with
	// any write to the index or bound register, any label, and any call.
	idxFacts map[int]idxFact
	// frameAddrs: register -> the frame address it holds, relative to the
	// entry sp (`add xN, sp, #imm`): the base of an owned array in the
	// frame. Memory through it is checked against the declared frame like
	// `[sp, #imm]`; the fact dies with a write to the register, a label, or
	// a call.
	frameAddrs map[int]int64
	// The label fixpoint: assumed guard states entering each label (nil on
	// the first, optimistic pass), the meet of the states arriving there
	// during this pass, and the conservative fallback that forgets all.
	labelIn        map[string]*guardState
	labelArrive    map[string]*guardState
	forgetAtLabels bool
	// calleeSaved tracks x19–x30: the caller's state, readable on entry,
	// writable only after being saved to the frame, and restored from the
	// same absolute slot before every ret (docs/spec/94-assembler.md §7).
	calleeSaved map[int]*savedState
	// calleeSavedV tracks d8–d15: the low 64 bits of v8–v15 are the
	// caller's under AAPCS64, with the same save/restore obligation.
	calleeSavedV map[int]*savedState

	// state
	written      map[int]bool
	writtenV     map[int]bool
	writtenP     map[int]bool
	flagsValid   bool
	disp         int64 // bytes the sp has moved below entry
	dispKnown    bool
	labelDisp    map[string]int64
	pendingDisp  map[string]int64
	labels       map[string]bool
	unreachable  bool
	alignBytes   int64 // current align region stride, 0 when none
	regionInstrs int64 // instructions since the region's align directive
	alignLine    int
}

// savedState is one callee-saved register's obligation: saved at an
// absolute frame address (relative to entry sp), written since, restored
// since the last write.
type savedState struct {
	saved    bool
	slot     int64
	written  bool
	restored bool
}

func calleeSavedRegister(num int) bool { return num >= 19 && num <= 30 }

// calleeSavedVector reports v8–v15, whose d views the callee preserves.
func calleeSavedVector(num int) bool { return num >= 8 && num <= 15 }

// spanParam is a span/view parameter's contract: two consecutive general
// registers (base pointer, then the 32-bit length in the low half of the
// next register — its upper half is padding and is never consulted).
type spanParam struct {
	baseReg  int
	lenReg   int
	elem     int64
	writable bool
}

// spanFact is the live knowledge about a bound span base register. hasMin
// holds after a dominating guard `cmp wL, #N` + `b.lo <fail>`: on the
// fall-through path len >= N, so offsets below N*elem are in bounds.
type spanFact struct {
	lenReg   int
	elem     int64
	writable bool
	hasMin   bool
	minLen   int64
}

// cmpFact remembers a 32-bit `cmp wA, #N` or `cmp wA, wB` for exactly the
// next instruction, which must be the guarding branch: `b.lo` after
// comparing a span length with N proves len >= N; `b.hs` after comparing
// an index with N or with a length register proves index < N / index < len.
type cmpFact struct {
	valid    bool
	left     int   // the compared register
	rightReg int   // the register compared against, or -1 for an immediate
	imm      int64 // the immediate compared against
}

// idxFact: the register is below an immediate bound (boundReg == -1) or
// below the value of another register (a span length register).
type idxFact struct {
	boundReg int
	bound    int64
}

// spanShape recognizes span ([*]T) and view ([]T) parameter types of
// fixed-width elements, returning the element size and writability.
func spanShape(expr ast.Expression) (elem int64, writable bool, ok bool) {
	indexExpr, isIndex := expr.(*ast.IndexExpression)
	if !isIndex || indexExpr.Dot {
		return 0, false, false
	}
	marker, isMarker := indexExpr.Index.(*ast.Identifier)
	if !isMarker || (marker.Value != "*" && marker.Value != "") {
		return 0, false, false
	}
	switch typeText(indexExpr.Left) {
	case "u8", "i8", "byte":
		elem = 1
	case "u16", "i16":
		elem = 2
	case "u32", "i32", "rune", "f32":
		elem = 4
	case "u64", "i64", "f64":
		elem = 8
	default:
		return 0, false, false
	}
	return elem, marker.Value == "*", true
}

func (c *checker) errorf(line int, format string, args ...interface{}) {
	c.errors = append(c.errors, fmt.Sprintf("%s:%d: %s", c.fn.Name, line, fmt.Sprintf(format, args...)))
}

// --- signature ---------------------------------------------------------

func typeText(expr ast.Expression) string {
	if expr == nil {
		return "()"
	}
	return expr.String()
}

func (c *checker) checkSignature(decl *ast.FunctionStatement) {
	sig := c.fn.Signature
	if decl == nil {
		c.errorf(c.fn.Line, "no Oak declaration named %s for this asm function", c.fn.Name)
		return
	}
	if len(sig.Parameters) != len(decl.Parameters) {
		c.errorf(c.fn.Line, "signature mismatch: asm unit declares %d parameters, Oak declares %d", len(sig.Parameters), len(decl.Parameters))
		return
	}
	for i, param := range sig.Parameters {
		other := decl.Parameters[i]
		if param.Name.Value != other.Name.Value || typeText(param.Type) != typeText(other.Type) || param.Variadic != other.Variadic {
			c.errorf(c.fn.Line, "signature mismatch at parameter %d: asm unit has %s: %s, Oak declaration has %s: %s",
				i+1, param.Name.Value, typeText(param.Type), other.Name.Value, typeText(other.Type))
			return
		}
	}
	if typeText(sig.ReturnType) != typeText(decl.ReturnType) {
		c.errorf(c.fn.Line, "signature mismatch: asm unit returns %s, Oak declaration returns %s", typeText(sig.ReturnType), typeText(decl.ReturnType))
	}
}

// contractClass maps a boundary type to its register class; v1 admits the
// fixed-width integers, Bool, and simd vectors.
func contractClass(expr ast.Expression) (RegClass, bool) {
	switch typeText(expr) {
	case "u8", "u16", "u32", "i8", "i16", "i32", "Bool", "byte", "rune":
		return ClassW, true
	case "u64", "i64":
		return ClassX, true
	case "f32", "f64":
		return ClassV, true // AAPCS64: floating-point values travel in v0–v7 (s/d views)
	}
	if strings.HasPrefix(typeText(expr), "simd.") {
		return ClassV, true
	}
	return 0, false
}

// floatView is the scalar view a floating-point parameter or result binds
// as: "s" for f32, "d" for f64, "" for a simd vector.
func floatView(expr ast.Expression) string {
	switch typeText(expr) {
	case "f32":
		return "s"
	case "f64":
		return "d"
	}
	return ""
}

// bindContract assigns AAPCS64 contract registers (x0..x7 / v0..v7) and
// verifies every parameter is bound explicitly at its class.
func (c *checker) bindContract() {
	c.paramClass = map[string]RegClass{}
	c.paramRegister = map[string]int{}
	c.paramView = map[string]string{}
	c.bound = map[int]bool{}
	c.spans = map[int]*spanFact{}
	c.idxFacts = map[int]idxFact{}
	c.spanParams = map[string]spanParam{}
	nextGeneral, nextVector := 0, 0
	for _, param := range c.fn.Signature.Parameters {
		if elem, writable, isSpan := spanShape(param.Type); isSpan {
			if nextGeneral > 6 {
				c.errorf(c.fn.Line, "span parameter %s needs two registers; the integer register contract is exhausted", param.Name.Value)
				continue
			}
			c.paramClass[param.Name.Value] = ClassX
			c.paramRegister[param.Name.Value] = nextGeneral
			c.spanParams[param.Name.Value] = spanParam{baseReg: nextGeneral, lenReg: nextGeneral + 1, elem: elem, writable: writable}
			nextGeneral += 2
			continue
		}
		class, ok := contractClass(param.Type)
		if !ok {
			c.errorf(c.fn.Line, "parameter %s: type %s cannot cross the asm boundary in v1 (fixed-width integers, Bool, simd vectors)", param.Name.Value, typeText(param.Type))
			continue
		}
		c.paramClass[param.Name.Value] = class
		c.paramView[param.Name.Value] = floatView(param.Type)
		if class == ClassV {
			if nextVector > 7 {
				c.errorf(c.fn.Line, "more than eight vector parameters exceed the register contract")
				continue
			}
			c.paramRegister[param.Name.Value] = nextVector
			nextVector++
		} else {
			if nextGeneral > 7 {
				c.errorf(c.fn.Line, "more than eight integer parameters exceed the register contract")
				continue
			}
			c.paramRegister[param.Name.Value] = nextGeneral
			nextGeneral++
		}
	}

	ret := typeText(c.fn.Signature.ReturnType)
	switch ret {
	case "()":
		c.hasResult = false
	case "never":
		c.never = true
	default:
		class, ok := contractClass(c.fn.Signature.ReturnType)
		if !ok {
			c.errorf(c.fn.Line, "return type %s cannot cross the asm boundary in v1", ret)
		}
		c.hasResult = true
		c.resultClass = class
	}

	seen := map[string]bool{}
	for _, binding := range c.fn.Bindings {
		class, isParam := c.paramClass[binding.Param]
		if !isParam {
			c.errorf(binding.Line, "bind: %s is not a parameter of %s", binding.Param, c.fn.Name)
			continue
		}
		if seen[binding.Param] {
			c.errorf(binding.Line, "bind: parameter %s bound twice", binding.Param)
			continue
		}
		seen[binding.Param] = true
		want := c.paramRegister[binding.Param]
		if span, isSpan := c.spanParams[binding.Param]; isSpan {
			if binding.Length == nil {
				c.errorf(binding.Line, "bind: span parameter %s binds a pair: bind x%d, w%d = %s (base pointer, 32-bit length)", binding.Param, span.baseReg, span.lenReg, binding.Param)
				continue
			}
			if binding.Register.Class != ClassX || binding.Register.Num != span.baseReg ||
				binding.Length.Class != ClassW || binding.Length.Num != span.lenReg {
				c.errorf(binding.Line, "bind: span parameter %s arrives as x%d (base), w%d (length; the upper half of x%d is padding), not %s, %s", binding.Param, span.baseReg, span.lenReg, span.lenReg, binding.Register.Text, binding.Length.Text)
				continue
			}
			c.bound[span.baseReg] = true
			c.bound[span.lenReg] = true
			c.spans[span.baseReg] = &spanFact{lenReg: span.lenReg, elem: span.elem, writable: span.writable}
			continue
		}
		if binding.Length != nil {
			c.errorf(binding.Line, "bind: parameter %s is a scalar and binds one register", binding.Param)
			continue
		}
		if view := c.paramView[binding.Param]; view != "" && binding.Register.Vec != view {
			c.errorf(binding.Line, "bind: floating-point parameter %s arrives in %s%d, not %s", binding.Param, view, want, binding.Register.Text)
			continue
		}
		if binding.Register.Class != class || binding.Register.Num != want {
			c.errorf(binding.Line, "bind: parameter %s arrives in %s%d (%s), not %s", binding.Param, classPrefix(class), want, class, binding.Register.Text)
			continue
		}
		c.bound[binding.Register.Num] = true
	}
	for _, param := range c.fn.Signature.Parameters {
		if _, isParam := c.paramClass[param.Name.Value]; isParam && !seen[param.Name.Value] {
			c.errorf(c.fn.Line, "parameter %s is never bound: bindings are written, not inferred (bind %s%d = %s)", param.Name.Value, classPrefix(c.paramClass[param.Name.Value]), c.paramRegister[param.Name.Value], param.Name.Value)
		}
	}
}

func classPrefix(class RegClass) string {
	switch class {
	case ClassW:
		return "w"
	case ClassV:
		return "v"
	}
	return "x"
}

func (c *checker) declareClobbers() {
	c.clobbered = map[int]bool{}
	c.clobberV = map[int]bool{}
	c.clobberP = map[int]bool{}
	for _, reg := range c.fn.Clobbers {
		switch reg.Class {
		case ClassSP:
			c.errorf(c.fn.Line, "clobber: sp is never a clobber; declare a frame")
		case ClassV, ClassZ:
			c.clobberV[reg.Num] = true // zN is vN with its scalable upper part
		case ClassP, ClassPN:
			c.clobberP[reg.Num] = true
		case ClassZA, ClassZT:
			c.errorf(c.fn.Line, "clobber: the ZA array is enabled by smstart, not clobbered")
		default:
			if reg.ZeroRegister() {
				c.errorf(c.fn.Line, "clobber: the zero register cannot be clobbered")
				continue
			}
			c.clobbered[reg.Num] = true
		}
	}
}

// --- the walk ----------------------------------------------------------

func (c *checker) walk() {
	c.written = map[int]bool{}
	c.writtenV = map[int]bool{}
	c.writtenP = map[int]bool{}
	c.frameAddrs = map[int]int64{}
	c.labelDisp = map[string]int64{}
	c.pendingDisp = map[string]int64{}
	c.labels = map[string]bool{}
	c.dispKnown = true
	c.calleeSaved = map[int]*savedState{}
	for num := 19; num <= 30; num++ {
		c.calleeSaved[num] = &savedState{}
	}
	c.calleeSavedV = map[int]*savedState{}
	for num := 8; num <= 15; num++ {
		c.calleeSavedV[num] = &savedState{}
	}

	// Labels are known up front so forward branches resolve.
	for _, item := range c.fn.Items {
		if label, ok := item.(Label); ok {
			if c.labels[label.Name] {
				c.errorf(label.Line, "duplicate label %s", label.Name)
			}
			c.labels[label.Name] = true
		}
	}

	terminated := false
	for _, item := range c.fn.Items {
		switch it := item.(type) {
		case Label:
			c.enterLabel(it)
			terminated = false
		case Align:
			// An aligned region is an entry point the hardware (or a
			// vector-table dispatch) may reach directly: control starts
			// fresh there — sp at displacement 0, flags unknown. Falling
			// INTO an entry with a live frame is refused.
			c.closeRegion(it.Line)
			if !c.unreachable && c.dispKnown && c.disp != 0 && c.regionInstrs > 0 {
				c.errorf(it.Line, "fall-through into an aligned entry with sp displacement %d: release the frame or end the previous region", c.disp)
			}
			c.alignBytes = it.Bytes
			c.regionInstrs = 0
			c.alignLine = it.Line
			c.unreachable = false
			c.disp = 0
			c.dispKnown = true
			c.flagsValid = false
			terminated = false
		case Instruction:
			if c.unreachable {
				c.errorf(it.Line, "unreachable instruction after an unconditional transfer; start a label")
				c.unreachable = false
			}
			c.regionInstrs++
			terminated = c.instruction(it)
		}
	}
	c.closeRegion(0)
	if !terminated {
		c.errorf(c.fn.Line, "control falls off the end of %s: end with ret, b, or eret", c.fn.Name)
	}
	for name := range c.pendingDisp {
		if !c.labels[name] {
			c.errorf(c.fn.Line, "branch to undefined label %s", name)
		}
	}
}

func (c *checker) closeRegion(line int) {
	if c.alignBytes == 0 {
		return
	}
	if c.regionInstrs*4 > c.alignBytes {
		c.errorf(c.alignLine, "align %d region holds %d instructions (%d bytes), exceeding its %d-byte stride", c.alignBytes, c.regionInstrs, c.regionInstrs*4, c.alignBytes)
	}
}

func (c *checker) enterLabel(label Label) {
	// A label merges control: its sp displacement must agree with every
	// branch that targets it, and flags are conservatively unknown.
	if !c.unreachable {
		c.arrive(label.Name) // the fall-through predecessor
	}
	if expected, pending := c.pendingDisp[label.Name]; pending {
		if c.dispKnown && !c.unreachable && expected != c.disp {
			c.errorf(label.Line, "label %s reached with sp displacement %d by fall-through and %d by branch", label.Name, c.disp, expected)
		}
		c.disp = expected
		c.dispKnown = true
	} else if c.unreachable || !c.dispKnown {
		c.errorf(label.Line, "label %s has no known stack displacement: it is only reachable by a later branch", label.Name)
		c.dispKnown = true
		c.disp = 0
	}
	c.labelDisp[label.Name] = c.disp
	c.flagsValid = false
	c.unreachable = false
	// Guard facts at the label: the fixpoint's assumption for it — the meet
	// of every predecessor's facts — or, on the first pass (no assumption
	// yet) the optimistic carry-over, or under the conservative fallback
	// nothing at all.
	switch {
	case c.forgetAtLabels:
		c.forgetGuards()
	case c.labelIn == nil:
		c.pendingCmp = cmpFact{}
	default:
		if assumed, known := c.labelIn[label.Name]; known {
			c.applyGuards(assumed)
		} else {
			c.forgetGuards() // no predecessor reached it: unreachable label
		}
	}
}

// forgetGuards drops every span length guard: control merged (label) or
// left the function (call), so no fall-through fact survives.
func (c *checker) forgetGuards() {
	for _, fact := range c.spans {
		fact.hasMin = false
	}
	c.pendingCmp = cmpFact{}
	c.idxFacts = map[int]idxFact{}
	c.frameAddrs = map[int]int64{}
}

// instruction checks one instruction and reports whether it ends control.
func (c *checker) instruction(instr Instruction) bool {
	// A length comparison guards exactly the next instruction.
	guard := c.pendingCmp
	c.pendingCmp = cmpFact{}
	spec := instructionTable[instr.Mnemonic]
	if spec.tableForms && (len(spec.forms) == 0 || usesScalable(instr.Operands)) {
		return c.scalable(instr) // SVE/SME: Arm's templates are the forms (asm/isa_sme.go)
	}
	matched, ok := matchForm(spec, instr.Operands)
	if !ok {
		c.errorf(instr.Line, "%s: operands %s do not match any legal form (width discipline: X with X, W with W)", instr.Mnemonic, describeOperands(instr.Operands))
		return false
	}
	if spec.system && !c.fn.System {
		c.errorf(instr.Line, "%s requires the unit's `system` capability", instr.Mnemonic)
	}
	if c.sm {
		// Most Advanced SIMD is illegal in streaming mode; the encoding
		// table carries Arm's per-encoding rule.
		if _, _, e, err := encodeInstruction(instr, 0, map[string]int64{}); err == nil && e != nil {
			c.requireMode(instr, e.enc.Mode)
		}
	}
	for _, operand := range instr.Operands {
		switch operand.(type) {
		case Shifted, Extended:
			if !modifierAllowed(instr.Mnemonic, operand) {
				c.errorf(instr.Line, "%s takes no shifted or extended register operand", instr.Mnemonic)
			}
		}
	}
	if finding := vectorDiscipline(instr); finding != "" {
		c.errorf(instr.Line, "%s: %s", instr.Mnemonic, finding)
	}
	if imm, isImm := lastImmediate(instr.Operands); isImm && imm.Shift != 0 {
		vectorDest := false
		if reg, isReg := instr.Operands[0].(Register); isReg && reg.Class == ClassV {
			vectorDest = true // movi/mvni/orr/bic vector immediates take `lsl #n`
		}
		switch instr.Mnemonic {
		case "movz", "movk", "movn":
			if imm.Shift%16 != 0 || imm.Shift > 48 || imm.MSL {
				c.errorf(instr.Line, "%s: the immediate shift must be lsl #0, #16, #32, or #48", instr.Mnemonic)
			}
		case "add", "adds", "sub", "subs", "cmp", "cmn":
			if imm.Shift != 12 || imm.MSL {
				c.errorf(instr.Line, "%s: an immediate is shifted by lsl #12 or not at all", instr.Mnemonic)
			}
		default:
			if !vectorDest {
				c.errorf(instr.Line, "%s takes no shifted immediate", instr.Mnemonic)
			}
		}
	}

	switch instr.Mnemonic {
	case "b":
		return c.branch(instr, true)
	case "b.":
		if !c.flagsValid {
			c.errorf(instr.Line, "b.%s consumes flags no dominating instruction produced (cmp/adds/subs must precede it with no intervening label or call)", instr.Cond)
		}
		c.branch(instr, false)
		// `cmp wL, #N` then `b.lo fail`: the fall-through path knows
		// len >= N for every span whose length register is wL.
		if guard.valid && guard.rightReg < 0 && (instr.Cond == "lo" || instr.Cond == "cc") {
			for _, fact := range c.spans {
				if fact.lenReg == guard.left {
					fact.hasMin = true
					fact.minLen = guard.imm
				}
			}
		}
		// `cmp wI, wL` / `cmp wI, #K` then `b.hs exit`: the fall-through
		// path knows wI < len / wI < K — the index guard of a loop walking
		// a span (Oak.Assembler.index_access).
		if guard.valid && (instr.Cond == "hs" || instr.Cond == "cs") {
			c.idxFacts[guard.left] = idxFact{boundReg: guard.rightReg, bound: guard.imm}
		}
		return false
	case "retaa", "retab":
		return c.ret(instr) // an authenticated return
	case "braa", "brab", "braaz", "brabz":
		for _, reg := range registerOperands(instr.Operands) {
			c.read(instr, reg)
		}
		if c.disp != 0 {
			c.errorf(instr.Line, "%s with sp displacement %d: the frame must be fully released", instr.Mnemonic, c.disp)
		}
		c.unreachable = true
		return true
	case "blraa", "blrab", "blraaz", "blrabz":
		for _, reg := range registerOperands(instr.Operands) {
			c.read(instr, reg)
		}
		c.indirectCall(instr)
		return false
	case "bti", "sb", "dgh":
		return false
	case "wfet", "wfit":
		c.read(instr, instr.Operands[0].(Register))
		return false
	case "setf8", "setf16":
		c.read(instr, instr.Operands[0].(Register))
		c.flagsValid = true
		return false
	case "rmif":
		if !c.flagsValid {
			c.errorf(instr.Line, "rmif rotates flags no dominating instruction produced")
		}
		c.read(instr, instr.Operands[0].(Register))
		if shift := instr.Operands[1].(Immediate).Value; shift < 0 || shift > 63 {
			c.errorf(instr.Line, "rmif: shift %d is not below 64", shift)
		}
		if mask := instr.Operands[2].(Immediate).Value; mask < 0 || mask > 15 {
			c.errorf(instr.Line, "rmif: mask %d is not a 4-bit flag pattern", mask)
		}
		c.flagsValid = true
		return false
	case "axflag", "xaflag":
		if !c.flagsValid {
			c.errorf(instr.Line, "%s converts flags no dominating instruction produced", instr.Mnemonic)
		}
		return false
	case "fcadd", "fcmla":
		if rotation := instr.Operands[len(instr.Operands)-1].(Immediate).Value; rotation%90 != 0 || rotation < 0 || rotation > 270 || (instr.Mnemonic == "fcadd" && rotation != 90 && rotation != 270) {
			c.errorf(instr.Line, "%s: rotation #%d is not one of the encodable rotations", instr.Mnemonic, rotation)
		}
	case "br":
		// An indirect terminal transfer: the frame is released and the
		// callee-saved obligations met, as for ret; the target is unknown.
		c.read(instr, instr.Operands[0].(Register))
		if c.disp != 0 {
			c.errorf(instr.Line, "br with sp displacement %d: the frame must be fully released", c.disp)
		}
		for num := 19; num <= 30; num++ {
			if state := c.calleeSaved[num]; state.written && !state.restored {
				c.errorf(instr.Line, "br without restoring callee-saved x%d", num)
			}
		}
		c.unreachable = true
		return true
	case "blr":
		c.read(instr, instr.Operands[0].(Register))
		c.indirectCall(instr)
		return false
	case "brk":
		// A trap: control never continues.
		c.unreachable = true
		return true
	case "svc", "hvc", "smc":
		// An exception to a higher level: the handler owns the caller-saved
		// state, as a callee does.
		c.clobberCallerSaved()
		return false
	case "wfe", "wfi", "sev", "sevl", "yield", "csdb", "esb", "hint", "clrex", "ssbb", "pssbb":
		return false
	case "dc", "ic", "tlbi", "at", "cfp", "cpp", "dvp":
		// Maintenance operations read their address register.
		if reg, isReg := lastRegister(instr.Operands); isReg {
			c.read(instr, reg)
		}
		return false
	case "cfinv":
		if !c.flagsValid {
			c.errorf(instr.Line, "cfinv inverts flags no dominating instruction produced")
		}
		return false
	case "cbz", "cbnz", "tbz", "tbnz":
		// Compare-and-branch: reads its register, needs no flags; a bit
		// test names a bit inside the register.
		reg := instr.Operands[0].(Register)
		c.read(instr, reg)
		if imm, isBitTest := instr.Operands[1].(Immediate); isBitTest {
			if imm.Value < 0 || imm.Value >= int64(widthOf(reg.Class)) {
				c.errorf(instr.Line, "%s: bit %d is outside %s", instr.Mnemonic, imm.Value, reg.Text)
			}
		}
		c.branch(instr, false)
		return false
	case "bl":
		c.call(instr)
		return false
	case "ret":
		if len(instr.Operands) == 1 {
			c.read(instr, instr.Operands[0].(Register)) // ret xN: an explicit return address
		}
		return c.ret(instr)
	case "eret", "eretaa", "eretab":
		if !c.never && c.hasResult {
			c.errorf(instr.Line, "eret from a function with a result: exception return never delivers %s", typeText(c.fn.Signature.ReturnType))
		}
		c.unreachable = true
		return true
	case "mrs":
		c.systemRegister(instr, instr.Operands[1].(SysReg).Name, true)
		c.write(instr, instr.Operands[0].(Register))
		return false
	case "msr":
		if reg, isReg := instr.Operands[1].(Register); isReg {
			c.systemRegister(instr, instr.Operands[0].(SysReg).Name, false)
			c.read(instr, reg)
		}
		// `msr field, #imm` writes a PSTATE field from a constant; the
		// field names are the encoder's table.
		return false
	case "dmb", "dsb", "isb", "nop":
		return false
	}

	if spec.memory {
		c.memoryAccess(instr, matched)
		return false
	}
	// csel/cset consume flags under the same dominance rule as b.cond.
	if spec.readsFlags && !c.flagsValid {
		c.errorf(instr.Line, "%s consumes flags no dominating instruction produced (cmp/adds/subs must precede it with no intervening label or call)", instr.Mnemonic)
	}

	// Data processing: reads then write; sp arithmetic moves the frame.
	regs := registerOperands(instr.Operands)
	if len(regs) == 0 {
		return false
	}
	dest := regs[0]
	for _, source := range regs[1:] {
		c.read(instr, source)
	}
	if pacTransparent(instr.Mnemonic) {
		return false // signing the link register is not a tracked write
	}
	if pacInPlace(instr.Mnemonic) {
		c.read(instr, dest)
	}
	switch instr.Mnemonic {
	case "bfm", "sbfm", "ubfm":
		// Raw bit-field moves: rotation and field end both below the width.
		for _, i := range []int{2, 3} {
			if v := instr.Operands[i].(Immediate).Value; v < 0 || v >= int64(widthOf(dest.Class)) {
				c.errorf(instr.Line, "%s: immediate %d is not below the width of %s", instr.Mnemonic, v, dest.Text)
			}
		}
		if instr.Mnemonic == "bfm" {
			c.read(instr, dest)
		}
	case "ubfx", "ubfiz", "sbfx", "sbfiz", "bfi", "bfxil", "bfc":
		// Bit-field immediates: a field of width >= 1 starting at lsb >= 0,
		// inside the register (bfc has no source operand).
		lsbAt := 2
		if instr.Mnemonic == "bfc" {
			lsbAt = 1
		}
		lsb, width := instr.Operands[lsbAt].(Immediate).Value, instr.Operands[lsbAt+1].(Immediate).Value
		if lsb < 0 || width < 1 || lsb+width > int64(widthOf(dest.Class)) {
			c.errorf(instr.Line, "%s: field [%d, %d) is not inside %s", instr.Mnemonic, lsb, lsb+width, dest.Text)
		}
		switch instr.Mnemonic {
		case "bfi", "bfxil", "bfc":
			c.read(instr, dest) // the insert or clear keeps the destination's other bits
		}
	case "movk":
		c.read(instr, dest) // the insert keeps the other halfwords
	case "extr":
		if lsb := instr.Operands[3].(Immediate).Value; lsb < 0 || lsb >= int64(widthOf(dest.Class)) {
			c.errorf(instr.Line, "extr: lsb %d is not below the width of %s", lsb, dest.Text)
		}
	case "ccmp", "ccmn":
		// A conditional compare reads its first operand and an nzcv immediate.
		if nzcv := instr.Operands[2].(Immediate).Value; nzcv < 0 || nzcv > 15 {
			c.errorf(instr.Line, "ccmp: nzcv immediate %d is not a 4-bit flag pattern", nzcv)
		}
		c.read(instr, dest)
		c.flagsValid = true
		return false
	}
	if instr.Mnemonic == "cmp" || instr.Mnemonic == "tst" || instr.Mnemonic == "cmn" {
		c.read(instr, dest) // cmp/cmn/tst: the first operand is a source
		c.flagsValid = true
		// Only 32-bit comparisons guard: a span length lives in the low half
		// of its register (the upper half is padding the contract never
		// defines), and an index is a 32-bit element count.
		if instr.Mnemonic == "cmp" && dest.Class == ClassW {
			switch right := instr.Operands[1].(type) {
			case Immediate:
				c.pendingCmp = cmpFact{valid: true, left: dest.Num, rightReg: -1, imm: right.Value}
			case Register:
				if right.Class == ClassW && !right.ZeroRegister() {
					c.pendingCmp = cmpFact{valid: true, left: dest.Num, rightReg: right.Num}
				}
			}
		}
		return false
	}
	if dest.Class == ClassSP {
		imm, isImm := instr.Operands[2].(Immediate)
		if !isImm {
			c.errorf(instr.Line, "sp arithmetic needs an immediate")
			return false
		}
		if instr.Mnemonic == "sub" {
			c.moveSP(instr, imm.Value)
		} else {
			c.moveSP(instr, -imm.Value)
		}
		return false
	}
	c.write(instr, dest)
	if instr.Mnemonic == "add" && len(regs) == 2 && regs[1].Class == ClassSP && dest.Class == ClassX {
		// `add xN, sp, #imm`: xN holds a frame address (an owned array's base).
		if imm, isImm := instr.Operands[2].(Immediate); isImm {
			if !c.dispKnown {
				c.errorf(instr.Line, "add %s, sp: the sp displacement is unknown here", dest.Text)
			} else {
				c.frameAddrs[dest.Num] = -c.disp + imm.Value
			}
		}
	}
	if spec.setsFlags {
		c.flagsValid = true
	}
	return false
}

func registerOperands(operands []Operand) []Register {
	var regs []Register
	for _, operand := range operands {
		if list, isList := operand.(RegisterList); isList {
			regs = append(regs, list.Regs...)
			continue
		}
		if reg, ok := operandRegister(operand); ok {
			regs = append(regs, reg)
		}
	}
	return regs
}

func lastImmediate(operands []Operand) (Immediate, bool) {
	for _, operand := range operands {
		if imm, ok := operand.(Immediate); ok {
			return imm, true
		}
	}
	return Immediate{}, false
}

func describeOperands(operands []Operand) string {
	parts := make([]string, 0, len(operands))
	for _, operand := range operands {
		switch o := operand.(type) {
		case Register:
			parts = append(parts, o.Text+":"+o.Class.String())
		case Immediate:
			parts = append(parts, fmt.Sprintf("#%d", o.Value))
		case Memory:
			parts = append(parts, "[mem]")
		default:
			parts = append(parts, operand.operandKind())
		}
	}
	return "(" + strings.Join(parts, ", ") + ")"
}

// read enforces "no uninitialized reads": a source must be bound, written,
// sp, or a zero register.
func (c *checker) read(instr Instruction, reg Register) {
	switch reg.Class {
	case ClassSP, ClassZA, ClassZT:
		return
	case ClassV, ClassZ:
		if c.writtenV[reg.Num] {
			return
		}
		if calleeSavedVector(reg.Num) && !c.vZeroed {
			return // d8–d15 carry the caller's values on entry
		}
		if c.boundVector(reg.Num) && !c.vZeroed {
			return
		}
		if c.boundVector(reg.Num) {
			c.errorf(instr.Line, "read of %s after smstart/smstop zeroed the vector registers (the bound value is gone)", reg.Text)
			return
		}
		c.errorf(instr.Line, "read of %s before any write or binding", reg.Text)
		return
	case ClassP, ClassPN:
		if !c.writtenP[reg.Num] {
			c.errorf(instr.Line, "read of %s before any write (predicates hold no value on entry, and smstart zeroes them)", reg.Text)
		}
		return
	}
	if reg.ZeroRegister() || calleeSavedRegister(reg.Num) {
		return // callee-saved registers carry the caller's values on entry
	}
	if !c.bound[reg.Num] && !c.written[reg.Num] {
		c.errorf(instr.Line, "read of %s before any write or binding (uninitialized register)", reg.Text)
	}
}

func (c *checker) boundVector(num int) bool {
	for name, class := range c.paramClass {
		if class == ClassV && c.paramRegister[name] == num {
			return true
		}
	}
	return false
}

// write enforces authority: a destination is a bound parameter register,
// the result register, or a declared clobber. wN/xN alias: writing either
// width is a write of the physical register.
func (c *checker) write(instr Instruction, reg Register) {
	if reg.Class == ClassSP {
		c.errorf(instr.Line, "sp may only move by add/sub sp, sp, #imm or pre/post-index addressing")
		return
	}
	if reg.Class == ClassV || reg.Class == ClassZ {
		if !c.clobberV[reg.Num] && !c.boundVector(reg.Num) && !(c.hasResult && c.resultClass == ClassV && reg.Num == 0) {
			c.errorf(instr.Line, "write to undeclared register %s: declare it with `clobber v%d`", reg.Text, reg.Num)
			return
		}
		if state, isSaved := c.calleeSavedV[reg.Num]; isSaved {
			if !state.saved {
				c.errorf(instr.Line, "write to callee-saved %s before saving it to the frame (str/stp its d view into the declared frame first; d8–d15 are the caller's under AAPCS64)", reg.Text)
				return
			}
			state.written = true
			state.restored = false
		}
		c.writtenV[reg.Num] = true
		return
	}
	if reg.Class == ClassP || reg.Class == ClassPN {
		if !c.clobberP[reg.Num] {
			c.errorf(instr.Line, "write to undeclared predicate %s: declare it with `clobber p%d`", reg.Text, reg.Num)
			return
		}
		c.writtenP[reg.Num] = true
		return
	}
	if reg.Class == ClassZA || reg.Class == ClassZT {
		return
	}
	if reg.ZeroRegister() {
		return
	}
	isResult := c.hasResult && c.resultClass != ClassV && reg.Num == 0
	if !c.bound[reg.Num] && !c.clobbered[reg.Num] && !isResult {
		c.errorf(instr.Line, "write to undeclared register %s: bind it, or declare it with `clobber %s`", reg.Text, reg.Text)
		return
	}
	if state, isSaved := c.calleeSaved[reg.Num]; isSaved {
		if !state.saved {
			c.errorf(instr.Line, "write to callee-saved %s before saving it to the frame (str/stp it into the declared frame first)", reg.Text)
			return
		}
		state.written = true
		state.restored = false
	}
	c.written[reg.Num] = true
	// Moving a span base forgets the span; touching a length register
	// forgets its guard; touching an index or its bound forgets the
	// index fact.
	delete(c.spans, reg.Num)
	for _, fact := range c.spans {
		if fact.lenReg == reg.Num {
			fact.hasMin = false
		}
	}
	delete(c.idxFacts, reg.Num)
	for index, fact := range c.idxFacts {
		if fact.boundReg == reg.Num {
			delete(c.idxFacts, index)
		}
	}
	delete(c.frameAddrs, reg.Num)
}

func (c *checker) moveSP(instr Instruction, delta int64) {
	if c.fn.Frame == 0 {
		c.errorf(instr.Line, "sp moves without a declared frame: add `frame N`")
		return
	}
	if delta%16 != 0 {
		c.errorf(instr.Line, "sp must stay 16-byte aligned (moved by %d)", delta)
	}
	c.disp += delta
	if c.disp < 0 || c.disp > c.fn.Frame {
		c.errorf(instr.Line, "sp displacement %d leaves the declared %d-byte frame", c.disp, c.fn.Frame)
	}
}

// memoryAccess bounds every access against the declared frame using the
// static sp displacement. Effective address relative to entry sp:
// -disp + offset (after a pre-index update); the access [addr, addr+size)
// must lie within [-frame, 0).
func (c *checker) memoryAccess(instr Instruction, matched form) {
	mem, _ := instr.Operands[len(instr.Operands)-1].(Memory)
	regs := registerOperands(instr.Operands[:len(instr.Operands)-1])
	if isAtomic(instr.Mnemonic) || isExclusiveStore(instr.Mnemonic) {
		c.atomicAccess(instr, matched, mem, regs)
		return
	}
	isStore := isStoreMnemonic(instr.Mnemonic)
	for _, reg := range regs {
		if isStore || isPrefetch(instr.Mnemonic) {
			c.read(instr, reg)
		}
	}
	if isPrefetch(instr.Mnemonic) {
		regs = nil // a hint: its registers are read, none written
	}
	if mem.Base.Class == ClassX {
		if fact, isSpan := c.spans[mem.Base.Num]; isSpan {
			c.spanAccess(instr, matched, mem, fact, regs, isStore)
			return
		}
		if addr, isFrame := c.frameAddrs[mem.Base.Num]; isFrame {
			c.frameArrayAccess(instr, matched, mem, addr, regs, isStore)
			return
		}
	}
	if mem.Base.Class != ClassSP {
		c.errorf(instr.Line, "memory operands go through the declared sp frame or a bound span base; %s is neither", mem.Base.Text)
		return
	}
	if mem.Index != nil {
		c.errorf(instr.Line, "%s: register-offset addressing walks a span, not the frame", instr.Mnemonic)
		return
	}
	if c.fn.Frame == 0 {
		c.errorf(instr.Line, "memory access without a declared frame: add `frame N`")
		return
	}
	size := accessBytes(instr.Mnemonic, matched[0])
	if len(regs) > 0 && regs[0].Class == ClassV {
		size = memorySizeReg(instr.Mnemonic, regs[0])
		if isStructureAccess(instr.Mnemonic) {
			size *= int64(len(regs))
		}
	}
	var slotBase int64
	switch mem.Mode {
	case MemPreIndex:
		c.moveSP(instr, -mem.Offset)
		c.checkAccess(instr, 0, size)
		slotBase = -c.disp
	case MemPostIndex:
		c.checkAccess(instr, 0, size)
		slotBase = -c.disp
		c.moveSP(instr, -mem.Offset)
	default:
		c.checkAccess(instr, mem.Offset, size)
		slotBase = -c.disp + mem.Offset
	}
	if len(regs) == 0 {
		return // prfm: a bounds-checked hint with no register
	}
	width := size / int64(len(regs))
	if isStore {
		// Saving a still-untouched callee-saved register records its slot
		// (x19–x30 whole, d8–d15 as their d view).
		for i, reg := range regs {
			if state := c.calleeSavedState(reg); state != nil && !state.written && !state.saved {
				state.saved = true
				state.slot = slotBase + int64(i)*width
			}
		}
		return
	}
	for i, reg := range regs {
		c.write(instr, reg)
		// Loading a callee-saved register back from its own slot restores it.
		if state := c.calleeSavedState(reg); state != nil && state.saved && state.slot == slotBase+int64(i)*width {
			state.restored = true
		}
	}
}

// calleeSavedState is the save/restore obligation a register carries: x19–x30,
// or v8–v15 accessed as its 64-bit d view; nil otherwise.
func (c *checker) calleeSavedState(reg Register) *savedState {
	switch {
	case reg.Class == ClassX:
		return c.calleeSaved[reg.Num]
	case reg.Class == ClassV && reg.Vec == "d":
		return c.calleeSavedV[reg.Num]
	}
	return nil
}

// frameArrayAccess admits memory through a register holding a frame address
// (`add xN, sp, #imm`): `[xN, #off]` must lie inside the declared frame, and
// `[xN, wI, uxtw #s]` needs a dominating constant index guard (`cmp wI, #K`
// then `b.hs <exit>`) with the K whole elements inside the frame — the
// owned array in the frame, bounds-checked like an Oak index.
func (c *checker) frameArrayAccess(instr Instruction, matched form, mem Memory, base int64, regs []Register, isStore bool) {
	if mem.Mode != MemOffset {
		c.errorf(instr.Line, "%s: a frame address is never moved; pre/post-index addressing is refused on %s", instr.Mnemonic, mem.Base.Text)
		return
	}
	size := accessBytes(instr.Mnemonic, matched[0])
	if len(regs) > 0 && regs[0].Class == ClassV {
		size = memorySizeReg(instr.Mnemonic, regs[0])
	}
	inFrame := func(lo, hi int64) bool { return lo >= -c.fn.Frame && hi <= 0 }
	if mem.Index == nil {
		if !inFrame(base+mem.Offset, base+mem.Offset+size) {
			c.errorf(instr.Line, "%s touches [%d, %d) relative to entry sp through %s, outside the declared %d-byte frame", instr.Mnemonic, base+mem.Offset, base+mem.Offset+size, mem.Base.Text, c.fn.Frame)
			return
		}
	} else {
		index := *mem.Index
		c.read(instr, index)
		if index.Class != ClassW || mem.Extend != "" && mem.Extend != "uxtw" {
			c.errorf(instr.Line, "%s: a frame array is indexed by a 32-bit element index, `[base, wI, uxtw #s]`; %s is not one", instr.Mnemonic, index.Text)
			return
		}
		if int64(1)<<uint(mem.Shift) != size {
			c.errorf(instr.Line, "%s: indexed access must move by whole elements: a %d-byte access needs `uxtw #%d`", instr.Mnemonic, size, log2(size))
			return
		}
		bound, guarded := c.idxFacts[index.Num]
		if !guarded || bound.boundReg >= 0 {
			c.errorf(instr.Line, "%s indexed by %s without a dominating constant index guard: `cmp %s, #K` then `b.hs <exit>` bounds the frame array's index", instr.Mnemonic, index.Text, index.Text)
			return
		}
		if !inFrame(base, base+bound.bound*size) {
			c.errorf(instr.Line, "%s: the guard admits %d elements of %d bytes at %d relative to entry sp, past the declared %d-byte frame", instr.Mnemonic, bound.bound, size, base, c.fn.Frame)
			return
		}
	}
	if !isStore {
		for _, reg := range regs {
			c.write(instr, reg)
		}
	}
}

// systemRegister checks a named system register against Arm's SysReg
// release: it must exist and admit the access direction. The
// `S<op0>_<op1>_<Cn>_<Cm>_<op2>` spelling names any encoding.
func (c *checker) systemRegister(instr Instruction, name string, read bool) {
	lower := strings.ToLower(name)
	if strings.HasPrefix(lower, "s") && strings.Count(lower, "_") == 4 {
		return
	}
	enc, known := systemRegisterEncodings[lower]
	if !known {
		c.errorf(instr.Line, "%s: %s is not a system register Arm's SysReg release names (spell an implementation-defined one S<op0>_<op1>_<Cn>_<Cm>_<op2>)", instr.Mnemonic, name)
		return
	}
	if read && !enc.Read {
		c.errorf(instr.Line, "mrs: %s is not readable", name)
	}
	if !read && !enc.Write {
		c.errorf(instr.Line, "msr: %s is not writable", name)
	}
}

// isStoreMnemonic: the instructions whose register operands are sources
// written to memory (a view refuses them; the executor never treats their
// register as written).
func isStoreMnemonic(mnemonic string) bool {
	switch mnemonic {
	case "str", "stp", "strb", "strh", "stur", "sturb", "sturh", "stlr", "stlrb", "stlrh", "stlur", "stlurb", "stlurh",
		"stnp", "sttr", "sttrb", "sttrh", "stllr", "stllrb", "stllrh":
		return true
	}
	return false
}

// isExclusiveStore: stxr/stlxr and their b/h forms — a status register
// written, a value read, a store through the base.
func isExclusiveStore(mnemonic string) bool {
	switch mnemonic {
	case "stxr", "stlxr", "stxrb", "stlxrb", "stxrh", "stlxrh", "stxp", "stlxp":
		return true
	}
	return false
}

// atomicAccess checks an exclusive store or an LSE atomic through a span:
// the base must be a guarded, writable span (every atomic may store), the
// access one element; the roles of the register operands depend on the
// operation — stxr writes its status register and reads the value, cas
// reads both and writes the compare register, the others read the source
// and write the destination.
func (c *checker) atomicAccess(instr Instruction, matched form, mem Memory, regs []Register) {
	if mem.Base.Class != ClassX {
		c.errorf(instr.Line, "%s: atomics address a span base, not the frame", instr.Mnemonic)
		return
	}
	fact, isSpan := c.spans[mem.Base.Num]
	if !isSpan {
		c.errorf(instr.Line, "%s through %s, which is not a bound span base", instr.Mnemonic, mem.Base.Text)
		return
	}
	if !fact.writable {
		c.errorf(instr.Line, "%s through %s: the parameter is a read-only view ([]T); atomics need a span ([*]T)", instr.Mnemonic, mem.Base.Text)
		return
	}
	var reads, writes []Register
	switch {
	case isExclusiveStore(instr.Mnemonic):
		writes, reads = regs[:1], regs[1:]
	case atomicBase(instr.Mnemonic) == "casp":
		reads, writes = regs, regs[:2]
	case atomicBase(instr.Mnemonic) == "cas":
		reads, writes = regs, regs[:1]
	case strings.HasPrefix(atomicBase(instr.Mnemonic), "st"):
		reads = regs // the result is discarded
	default:
		reads, writes = regs[:1], regs[1:]
	}
	for _, reg := range reads {
		c.read(instr, reg)
	}
	// The access is one element (or pair) at the base, sized by the value
	// registers (no offset form for atomics).
	c.spanAccess(instr, matched, mem, fact, reads, true)
	for _, reg := range writes {
		c.write(instr, reg)
	}
}

func lastRegister(operands []Operand) (Register, bool) {
	for i := len(operands) - 1; i >= 0; i-- {
		if reg, ok := operands[i].(Register); ok {
			return reg, true
		}
	}
	return Register{}, false
}

// clobberCallerSaved: after a call or an exception, x0–x17, v0–v7, and the
// flags belong to the callee.
func (c *checker) clobberCallerSaved() {
	for num := 0; num <= 17; num++ {
		if !c.bound[num] || num == 0 {
			delete(c.written, num)
		}
	}
	for num := 0; num <= 7; num++ {
		delete(c.writtenV, num)
	}
	// The call's result: x0 for an integer, v0 for a floating-point one (the
	// checker does not see the callee's signature; either is readable).
	c.written[0] = true
	c.writtenV[0] = true
	c.flagsValid = false
	c.forgetGuards()
}

// indirectCall is `blr xN`: a call to an unknown Oak-visible target.
func (c *checker) indirectCall(instr Instruction) {
	if !c.clobbered[30] {
		c.errorf(instr.Line, "blr writes the link register: declare `clobber x30`")
	}
	if lr := c.calleeSaved[30]; lr != nil {
		if !c.never && !lr.saved {
			c.errorf(instr.Line, "blr in a returning function before saving the link register")
		}
		lr.written = true
		lr.restored = false
	}
	c.clobberCallerSaved()
}

// spanAccess admits [base, #off] on a bound span only under a dominating
// length guard: with len >= N established, the access [off, off+size) must
// lie inside the N*elem bytes the guard proves (Oak.Assembler.span_access).
func (c *checker) spanAccess(instr Instruction, matched form, mem Memory, fact *spanFact, regs []Register, isStore bool) {
	if mem.Mode != MemOffset {
		c.errorf(instr.Line, "%s: a span base is never moved; pre/post-index addressing is refused on %s", instr.Mnemonic, mem.Base.Text)
		return
	}
	if isStore && !fact.writable {
		c.errorf(instr.Line, "%s through %s: the parameter is a read-only view ([]T); stores need a span ([*]T)", instr.Mnemonic, mem.Base.Text)
		return
	}
	size := accessBytes(instr.Mnemonic, matched[0])
	if len(regs) > 0 {
		size = memorySizeReg(instr.Mnemonic, regs[0])
		if isStructureAccess(instr.Mnemonic) {
			size *= int64(len(regs))
		}
	}
	if mem.Index != nil {
		c.indexedSpanAccess(instr, mem, fact, size, regs, isStore)
		return
	}
	if mem.Offset < 0 {
		c.errorf(instr.Line, "%s: negative offset %d reaches before the span", instr.Mnemonic, mem.Offset)
		return
	}
	if !fact.hasMin {
		c.errorf(instr.Line, "%s through %s without a dominating bounds guard: `cmp w%d, #N` then `b.lo <fail>` proves len >= N for the fall-through path", instr.Mnemonic, mem.Base.Text, fact.lenReg)
		return
	}
	if mem.Offset+size > fact.elem*fact.minLen {
		c.errorf(instr.Line, "%s touches span bytes [%d, %d) but the guard proves only %d elements (%d bytes)", instr.Mnemonic, mem.Offset, mem.Offset+size, fact.minLen, fact.elem*fact.minLen)
		return
	}
	if mem.Offset%size != 0 && size <= 8 {
		c.errorf(instr.Line, "%s: offset %d is not aligned to the %d-byte access", instr.Mnemonic, mem.Offset, size)
	}
	if !isStore {
		for _, reg := range regs {
			c.write(instr, reg)
		}
	}
}

// indexedSpanAccess admits [base, wI, uxtw #s] on a bound span: the access
// is one whole element (1<<s == size == elem) at element index wI, and a
// dominating guard proved wI below the span's length — directly (`cmp wI,
// wL; b.hs`) or through a constant the length guard covers (`cmp wI, #K;
// b.hs` with len >= K established). Then (wI+1)*elem <= elem*len
// (Oak.Assembler.index_access).
func (c *checker) indexedSpanAccess(instr Instruction, mem Memory, fact *spanFact, size int64, regs []Register, isStore bool) {
	index := *mem.Index
	c.read(instr, index)
	if index.Class != ClassW || mem.Extend != "" && mem.Extend != "uxtw" {
		c.errorf(instr.Line, "%s: a span is walked by a 32-bit element index, `[base, wI, uxtw #s]`; %s is not one", instr.Mnemonic, index.Text)
		return
	}
	if size != fact.elem || int64(1)<<uint(mem.Shift) != size {
		c.errorf(instr.Line, "%s: indexed access must move by whole elements: a %d-byte access over %d-byte elements needs `uxtw #%d` and a matching register width", instr.Mnemonic, size, fact.elem, log2(fact.elem))
		return
	}
	bound, guarded := c.idxFacts[index.Num]
	switch {
	case !guarded:
		c.errorf(instr.Line, "%s indexed by %s without a dominating index guard: `cmp %s, w%d` then `b.hs <exit>` proves the index below the span's length for the fall-through path", instr.Mnemonic, index.Text, index.Text, fact.lenReg)
		return
	case bound.boundReg == fact.lenReg:
		// index < len: in bounds.
	case bound.boundReg < 0 && fact.hasMin && bound.bound <= fact.minLen:
		// index < K <= len.
	case bound.boundReg < 0:
		c.errorf(instr.Line, "%s: the guard proves %s < %d but the span's proven minimum length is %d", instr.Mnemonic, index.Text, bound.bound, fact.minLen)
		return
	default:
		c.errorf(instr.Line, "%s: %s is guarded against w%d, which is not this span's length register (w%d)", instr.Mnemonic, index.Text, bound.boundReg, fact.lenReg)
		return
	}
	if !isStore {
		for _, reg := range regs {
			c.write(instr, reg)
		}
	}
}

func log2(n int64) int {
	shift := 0
	for n > 1 {
		n >>= 1
		shift++
	}
	return shift
}

func (c *checker) checkAccess(instr Instruction, offset, size int64) {
	addr := -c.disp + offset
	if addr < -c.fn.Frame || addr+size > 0 {
		c.errorf(instr.Line, "%s touches [%d, %d) relative to entry sp, outside the declared %d-byte frame [-%d, 0)", instr.Mnemonic, addr, addr+size, c.fn.Frame, c.fn.Frame)
	}
	if offset%size != 0 && size <= 8 {
		c.errorf(instr.Line, "%s: offset %d is not aligned to the %d-byte access", instr.Mnemonic, offset, size)
	}
}

func (c *checker) branch(instr Instruction, unconditional bool) bool {
	target := instr.Operands[len(instr.Operands)-1].(Symbol).Name // b/b.cond: the only operand; cbz/tbz: the last
	if c.labels[target] {
		c.arrive(target) // the branch-taken predecessor, with the facts held here
		if recorded, seen := c.labelDisp[target]; seen {
			if recorded != c.disp {
				c.errorf(instr.Line, "branch to %s with sp displacement %d, label recorded %d", target, c.disp, recorded)
			}
		} else if expected, pending := c.pendingDisp[target]; pending {
			if expected != c.disp {
				c.errorf(instr.Line, "branch to %s with sp displacement %d, another branch expects %d", target, c.disp, expected)
			}
		} else {
			c.pendingDisp[target] = c.disp
		}
	} else if c.symbols[target] {
		if c.disp != 0 {
			c.errorf(instr.Line, "branch to function %s with sp displacement %d: restore the frame first", target, c.disp)
		}
	} else {
		c.errorf(instr.Line, "branch target %s is neither a label in %s nor an Oak-visible function", target, c.fn.Name)
	}
	if unconditional {
		c.unreachable = true
	}
	return unconditional
}

func (c *checker) call(instr Instruction) {
	target := instr.Operands[0].(Symbol).Name
	if !c.symbols[target] {
		c.errorf(instr.Line, "bl target %s is not an Oak-visible function", target)
	}
	if !c.clobbered[30] {
		c.errorf(instr.Line, "bl writes the link register: declare `clobber x30`")
	}
	if c.sm || c.za {
		c.errorf(instr.Line, "bl in streaming mode or with the ZA array enabled: Oak functions have no streaming interface — smstop first")
	}
	if lr := c.calleeSaved[30]; lr != nil {
		if !c.never && !lr.saved {
			c.errorf(instr.Line, "bl in a returning function before saving the link register: stp x29, x30 (or str x30) into the frame first")
		}
		lr.written = true
		lr.restored = false
	}
	// The callee owns x0–x17, v0–v7, and the flags under AAPCS64.
	for num := 0; num <= 17; num++ {
		if !c.bound[num] || num == 0 {
			delete(c.written, num)
		}
	}
	for num := 0; num <= 7; num++ {
		delete(c.writtenV, num)
	}
	// The call's result: x0 for an integer, v0 for a floating-point one (the
	// checker does not see the callee's signature; either is readable).
	c.written[0] = true
	c.writtenV[0] = true
	c.flagsValid = false
	c.forgetGuards()
}

func (c *checker) ret(instr Instruction) bool {
	if c.never {
		c.errorf(instr.Line, "ret from a function declared never to return")
	}
	if c.disp != 0 {
		c.errorf(instr.Line, "ret with sp displacement %d: the frame must be fully released", c.disp)
	}
	for num := 19; num <= 30; num++ {
		if state := c.calleeSaved[num]; state.written && !state.restored {
			c.errorf(instr.Line, "ret without restoring callee-saved x%d from its frame slot (ldr/ldp it from the slot it was saved to)", num)
		}
	}
	for num := 8; num <= 15; num++ {
		if state := c.calleeSavedV[num]; state.written && !state.restored {
			c.errorf(instr.Line, "ret without restoring callee-saved d%d from its frame slot (ldr/ldp its d view from the slot it was saved to)", num)
		}
	}
	if c.hasResult {
		if c.resultClass == ClassV {
			if !c.writtenV[0] && (!c.boundVector(0) || c.vZeroed) {
				c.errorf(instr.Line, "ret without producing the result in v0")
			}
		} else if !c.written[0] && !c.bound[0] {
			c.errorf(instr.Line, "ret without producing the result in %s0", classPrefix(c.resultClass))
		}
	}
	if c.sm || c.za {
		c.errorf(instr.Line, "ret with streaming mode or the ZA array still enabled: the caller is not streaming — smstop first")
	}
	c.unreachable = true
	return true
}
