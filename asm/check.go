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
	c := &checker{fn: fn, symbols: symbols}
	c.checkSignature(decl)
	if len(c.errors) != 0 {
		return c.errors
	}
	c.bindContract()
	c.declareClobbers()
	c.walk()
	return c.errors
}

type checker struct {
	fn      *Function
	symbols map[string]bool
	errors  []string

	// contract
	paramClass    map[string]RegClass // parameter -> width class
	paramRegister map[string]int      // parameter -> contract register number
	resultClass   RegClass
	hasResult     bool
	never         bool

	// authority
	bound     map[int]bool // register numbers bound to parameters
	clobbered map[int]bool // declared clobbers (general file)
	clobberV  map[int]bool // declared vector clobbers
	// spans: base register number -> the span it points at (typed pointer
	// parameters); guard facts live here and die with any write to the
	// base or length register, any label, and any call.
	spans      map[int]*spanFact
	spanParams map[string]spanParam
	pendingCmp cmpFact
	// calleeSaved tracks x19–x30: the caller's state, readable on entry,
	// writable only after being saved to the frame, and restored from the
	// same absolute slot before every ret (docs/spec/94-assembler.md §7).
	calleeSaved map[int]*savedState

	// state
	written      map[int]bool
	writtenV     map[int]bool
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

// cmpFact remembers a `cmp wL, #N` on a span length register for exactly
// the next instruction, which must be the guarding branch.
type cmpFact struct {
	valid  bool
	lenReg int
	imm    int64
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
	case "u32", "i32", "rune":
		elem = 4
	case "u64", "i64":
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
	}
	if strings.HasPrefix(typeText(expr), "simd.") {
		return ClassV, true
	}
	return 0, false
}

// bindContract assigns AAPCS64 contract registers (x0..x7 / v0..v7) and
// verifies every parameter is bound explicitly at its class.
func (c *checker) bindContract() {
	c.paramClass = map[string]RegClass{}
	c.paramRegister = map[string]int{}
	c.bound = map[int]bool{}
	c.spans = map[int]*spanFact{}
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
	for _, reg := range c.fn.Clobbers {
		switch reg.Class {
		case ClassSP:
			c.errorf(c.fn.Line, "clobber: sp is never a clobber; declare a frame")
		case ClassV:
			c.clobberV[reg.Num] = true
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
	c.labelDisp = map[string]int64{}
	c.pendingDisp = map[string]int64{}
	c.labels = map[string]bool{}
	c.dispKnown = true
	c.calleeSaved = map[int]*savedState{}
	for num := 19; num <= 30; num++ {
		c.calleeSaved[num] = &savedState{}
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
	c.forgetGuards()
}

// forgetGuards drops every span length guard: control merged (label) or
// left the function (call), so no fall-through fact survives.
func (c *checker) forgetGuards() {
	for _, fact := range c.spans {
		fact.hasMin = false
	}
	c.pendingCmp = cmpFact{}
}

// instruction checks one instruction and reports whether it ends control.
func (c *checker) instruction(instr Instruction) bool {
	// A length comparison guards exactly the next instruction.
	guard := c.pendingCmp
	c.pendingCmp = cmpFact{}
	spec := instructionTable[instr.Mnemonic]
	matched, ok := matchForm(spec, instr.Operands)
	if !ok {
		c.errorf(instr.Line, "%s: operands %s do not match any legal form (width discipline: X with X, W with W)", instr.Mnemonic, describeOperands(instr.Operands))
		return false
	}
	if spec.system && !c.fn.System {
		c.errorf(instr.Line, "%s requires the unit's `system` capability", instr.Mnemonic)
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
		if guard.valid && (instr.Cond == "lo" || instr.Cond == "cc") {
			for _, fact := range c.spans {
				if fact.lenReg == guard.lenReg {
					fact.hasMin = true
					fact.minLen = guard.imm
				}
			}
		}
		return false
	case "bl":
		c.call(instr)
		return false
	case "ret":
		return c.ret(instr)
	case "eret":
		if !c.never && c.hasResult {
			c.errorf(instr.Line, "eret from a function with a result: exception return never delivers %s", typeText(c.fn.Signature.ReturnType))
		}
		c.unreachable = true
		return true
	case "mrs":
		c.write(instr, instr.Operands[0].(Register))
		return false
	case "msr":
		c.read(instr, instr.Operands[1].(Register))
		return false
	case "dmb", "dsb", "isb", "nop":
		return false
	}

	if spec.memory {
		c.memoryAccess(instr, matched)
		return false
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
	if instr.Mnemonic == "cmp" {
		c.read(instr, dest) // cmp's first operand is a source
		c.flagsValid = true
		// Only the 32-bit view of a span length register guards: the upper
		// half of the register is padding the contract never defines.
		if imm, isImm := instr.Operands[1].(Immediate); isImm && dest.Class == ClassW {
			for _, fact := range c.spans {
				if fact.lenReg == dest.Num {
					c.pendingCmp = cmpFact{valid: true, lenReg: dest.Num, imm: imm.Value}
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
	if spec.setsFlags {
		c.flagsValid = true
	}
	return false
}

func registerOperands(operands []Operand) []Register {
	var regs []Register
	for _, operand := range operands {
		if reg, ok := operand.(Register); ok {
			regs = append(regs, reg)
		}
	}
	return regs
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
	case ClassSP:
		return
	case ClassV:
		if !c.writtenV[reg.Num] && !c.boundVector(reg.Num) {
			c.errorf(instr.Line, "read of v%d before any write or binding", reg.Num)
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
	if reg.Class == ClassV {
		if !c.clobberV[reg.Num] && !c.boundVector(reg.Num) && !(c.hasResult && c.resultClass == ClassV && reg.Num == 0) {
			c.errorf(instr.Line, "write to undeclared register v%d: declare it with `clobber v%d`", reg.Num, reg.Num)
			return
		}
		c.writtenV[reg.Num] = true
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
	// forgets its guard.
	delete(c.spans, reg.Num)
	for _, fact := range c.spans {
		if fact.lenReg == reg.Num {
			fact.hasMin = false
		}
	}
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
	isStore := instr.Mnemonic == "str" || instr.Mnemonic == "stp"
	for _, reg := range regs {
		if isStore {
			c.read(instr, reg)
		}
	}
	if mem.Base.Class == ClassX {
		if fact, isSpan := c.spans[mem.Base.Num]; isSpan {
			c.spanAccess(instr, matched, mem, fact, regs, isStore)
			return
		}
	}
	if mem.Base.Class != ClassSP {
		c.errorf(instr.Line, "memory operands go through the declared sp frame or a bound span base; %s is neither", mem.Base.Text)
		return
	}
	if c.fn.Frame == 0 {
		c.errorf(instr.Line, "memory access without a declared frame: add `frame N`")
		return
	}
	size := accessBytes(instr.Mnemonic, matched[0])
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
	width := size / int64(len(regs))
	if isStore {
		// Saving a still-untouched callee-saved register records its slot.
		for i, reg := range regs {
			if state, isSaved := c.calleeSaved[reg.Num]; isSaved && !state.written && !state.saved && reg.Class == ClassX {
				state.saved = true
				state.slot = slotBase + int64(i)*width
			}
		}
		return
	}
	for i, reg := range regs {
		c.write(instr, reg)
		// Loading a callee-saved register back from its own slot restores it.
		if state, isSaved := c.calleeSaved[reg.Num]; isSaved && state.saved && reg.Class == ClassX && state.slot == slotBase+int64(i)*width {
			state.restored = true
		}
	}
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
	target := instr.Operands[0].(Symbol).Name
	if c.labels[target] {
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
	c.written[0] = true // the call's result
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
	if c.hasResult {
		if c.resultClass == ClassV {
			if !c.writtenV[0] && !c.boundVector(0) {
				c.errorf(instr.Line, "ret without producing the result in v0")
			}
		} else if !c.written[0] && !c.bound[0] {
			c.errorf(instr.Line, "ret without producing the result in %s0", classPrefix(c.resultClass))
		}
	}
	c.unreachable = true
	return true
}
