package asm

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// The RV64 seam checker (docs/spec/94-assembler.md §9). What the AArch64
// checker enforces at the seams, restated for the LP64 psABI and an ISA
// without flags:
//
//   - the contract: integer parameters in a0–a7 in declaration order, a
//     span or view as the a_i/a_{i+1} pair, the result in a0; every
//     parameter bound explicitly at its contract register;
//   - writes only to bound registers, the result register a0, declared
//     clobbers (caller-saved t0–t6, a0–a7), or a callee-saved register
//     (s0–s11) and ra after they are saved to the frame; a save is
//     `sd reg, imm(sp)` and its restore `ld reg, imm(sp)` from the same
//     entry-relative slot, before ret;
//   - the frame: `frame N` (a multiple of 16), sp moved only by
//     `addi sp, sp, ±imm` in multiples of 16 within [0, N], every
//     `imm(sp)` access inside [-N, 0) aligned to its width; memory through
//     any other base is outside this increment and refused (fail closed);
//   - the comparison-branch rule: a conditional branch reads two registers,
//     so it needs them readable and nothing else (there are no flags);
//   - calls (`call`, `jal ra`, `jalr ra`) write ra and clobber the
//     caller-saved registers: ra must be saved to the frame first and
//     restored before ret; a1–a7 and t0–t6 are forgotten across the call,
//     a0 carries the callee's result;
//   - `ret` at displacement 0 with every written callee-saved register
//     restored and the result written; no ret from a `never` function; no
//     unreachable instruction and no fall-through past the end.
type rvChecker struct {
	fn      *Function
	symbols map[string]bool
	errors  []string

	hasResult bool
	never     bool
	// Composites under the LP64 psABI's integer calling convention
	// (docs/spec/94-assembler.md §9): a record or union of up to 16 bytes
	// travels as one or two 8-byte chunks in consecutive argument
	// registers, a larger one by reference; a result of up to 16 bytes
	// comes back in a0 (and a1), a larger one is written into the area
	// whose address the caller passes as a hidden first argument in a0.
	composites     map[string]rvComposite
	resultChunks   int  // a0 alone (1) or a0 and a1 (2)
	resultIndirect bool // a0 addresses the caller's result area on entry

	bound     map[int]bool // contract registers holding parameters
	clobbered map[int]bool // declared clobbers
	written   map[int]bool // registers written on this path
	freed     map[int]bool // caller-saved registers released by a call
	saved     map[int]*savedState

	// The floating-point file (LP64D): fa0–fa7 carry f32/f64 parameters and
	// fa0 the result; fs0–fs11 are callee-saved under the same obligation
	// as s0–s11; ft0–ft11 and the fa registers are clobberable.
	floatResult   bool
	fbound        map[int]bool
	fclobbered    map[int]bool
	fwritten      map[int]bool
	ffreed        map[int]bool
	fsaved        map[int]*savedState
	usesFloatFile bool

	disp        int64
	labelDisp   map[string]int64
	labels      map[string]bool
	unreachable bool

	// Span element memory (docs/spec/94-assembler.md §9). Every fact below
	// is forgotten at a label and on a write to a register it names, so a
	// guard protects exactly the straight-line code after it.
	writes  map[int]int          // register -> number of instructions writing it (whole body)
	spans   map[int]*rvSpan      // bound base register -> the span
	shl32   map[int]int          // register = raw length register << 32 (half of a normalization)
	lenNorm map[int]int          // register holding a span's length zero-extended -> its raw length register
	consts  map[int]int64        // register = constant (li)
	idx     map[int]rvIndexFact  // register < a normalized length register, or < a constant
	scaled  map[int]rvScaledFact // register = index << shift
	regions map[int]rvRegion     // register = the address of one element (size bytes)
	rem     map[int]rvRemFact    // register = normalized length - guarded index (the remaining count)
	// slack: register = normalized length - K under len >= K (`sub t, len,
	// k` after `bltu len, k, trap`): the bound of a K-element vector access
	// (docs/spec/94-assembler.md §9, Oak.RiscV.slack_guard).
	slack map[int]rvSlackFact
	// frameAddrs: register = an entry-relative frame address (`addi rD, sp,
	// imm`): an owned array's base (docs/spec/94-assembler.md §9). Memory
	// through it goes through a region formed under a constant index guard.
	frameAddrs map[int]int64
	// lenAlias: register = a copy of a span's raw length register (`mv rD,
	// aL`), the bound register it copies. A span's pair parked in
	// callee-saved registers survives a call this way: `mv sB, aB` makes
	// sB a base of the same span, `mv sL, aL` a raw length the
	// normalization pair may read (docs/spec/94-assembler.md §9).
	lenAlias map[int]int
	// rawDead marks a bound raw length register that has been written (a
	// call, or the unit itself): the span it identifies keeps its name,
	// but the register no longer holds the length, so it normalizes
	// nothing further. Copies and normalized copies made before stay valid.
	rawDead map[int]bool
	gen     map[int]int // write generation of each integer register (facts about a value name it)

	// The vector extension (docs/spec/94-assembler.md §9): v0–v31 are
	// caller-saved and clobberable, readable once written; the
	// configuration vsetvli establishes (SEW, and what the checker knows
	// about the AVL) is straight-line state, forgotten at labels and calls.
	vclobbered     map[int]bool
	vwritten       map[int]bool
	vcfg           *rvVectorConfig
	usesVectorFile bool
}

// rvComposite is a record parameter's arrival: its first register, how
// many chunks it spans (1 when indirect: the address of the caller's
// copy), and its size.
type rvComposite struct {
	reg, regs int
	size      int64
	indirect  bool
}

// rvRemFact: the register holds `len - idx` where len is the normalized
// length register lenReg and idx a register guarded below it (idxReg, at
// write generation idxGen), or the length itself (idxReg -1). Passed as
// the AVL of a vsetvli, it bounds vl: idx + vl ≤ len
// (Oak.RiscV.strip_access_in_bounds).
type rvRemFact struct {
	lenReg, idxReg, idxGen int
}

// rvVectorConfig is the vector configuration in effect: the element width
// SEW in bytes, LMUL in eighths (mf8 = 1 … m1 = 8 … m8 = 64), and the AVL —
// an immediate (vsetivli) or what is known of the register (vsetvli). vl ≤
// AVL always (RVV 1.0 §6.3, Oak.RiscV.vsetvlOK).
type rvVectorConfig struct {
	sew    int64
	lmul8  int64 // LMUL * 8: a fractional LMUL's group is one register (Oak.RiscV.groupOf)
	avlImm int64 // -1 when the AVL is a register
	rem    *rvRemFact
	line   int
}

// rv64LMULEighths maps a vtype LMUL spelling to LMUL * 8.
var rv64LMULEighths = map[string]int64{"mf8": 1, "mf4": 2, "mf2": 4, "m1": 8, "m2": 16, "m4": 32, "m8": 64}

// rv64LMULName spells LMUL * 8 as a vtype option, for messages.
func rv64LMULName(lmul8 int64) string {
	for name, v := range rv64LMULEighths {
		if v == lmul8 {
			return name
		}
	}
	return fmt.Sprintf("%d/8", lmul8)
}

// rv64GroupOf is the register count of an operand group at LMUL * 8
// (RVV 1.0 §3.4.2): LMUL registers at or above m1, one register below
// (Oak.RiscV.groupOf).
func rv64GroupOf(lmul8 int64) int64 {
	if lmul8 < 8 {
		return 1
	}
	return lmul8 / 8
}

// rv64GroupSingle names the operands that are one register whatever the
// LMUL: mask destinations (the comparisons), mask sources (vcpop.m, the
// v0 of vmerge.vvm and of a `v0.t` operand). RVV 1.0 §3.4.2: every other
// vector register operand is a group of LMUL registers aligned to LMUL.
func rv64GroupSingle(name string, position int) bool {
	switch name {
	case "vmseq.vv", "vmsne.vx", "vmslt.vx", "vmsltu.vx":
		return position == 0
	case "vredsum.vs", "vfredosum.vs":
		// A reduction's scalar input and result live in element 0 of a
		// single register, not a group (RVV 1.0 §14).
		return position == 0 || position == 2
	case "vmv.x.s", "vfmv.f.s":
		// Element 0 of the source, whatever the LMUL (RVV 1.0 §16.1, §16.2).
		return position == 1
	case "vcpop.m":
		return position == 1
	case "vmerge.vvm":
		return position == 3
	}
	return false
}

// rvSpan is the live knowledge about a bound span base: the LP64 pair
// leaves the u32 length in the low half of its register with padding
// above it, so a comparison against the raw register proves nothing; a
// bound needs the normalized copy (slli 32 then srli 32).
type rvSpan struct {
	rawLen   int
	elem     int64
	writable bool
	hasMin   bool
	minLen   int64
}

// rvIndexFact: the register is below a normalized length register
// (lenReg >= 0) or below a constant (lenReg < 0, bound). With slack K > 0
// the fact is idx + K <= len instead: K elements from idx lie inside the
// span (Oak.RiscV.slack_access_in_bounds).
type rvIndexFact struct {
	lenReg int
	bound  int64
	slack  int64
}

// rvSlackFact: the register holds len - K for the normalized length in
// lenReg, formed under len >= K.
type rvSlackFact struct {
	lenReg int
	k      int64
}

// rvScaledFact: the register is a guarded index shifted left by shift.
// The guard is copied at the shift (the index register may be the
// destination itself, `slli t2, t2, 3`).
type rvScaledFact struct {
	guard  rvIndexFact
	shift  int
	idxReg int // the index register the scaled value came from, at generation idxGen
	idxGen int
}

// rvRegion: the register is the address of one element of a span (size
// bytes); rawLen names the span, idxReg/idxGen the guarded index the
// address was formed from (-2 when the guard was a constant bound), so a
// vector configuration over `len - idx` can be matched to it.
type rvRegion struct {
	size     int64
	writable bool
	rawLen   int
	idxReg   int
	idxGen   int
	// lanes: how many elements from the address the guard proved inside
	// the span — one under an index guard, K under a slack guard.
	lanes int64
	// frame marks an element of an owned array in the frame (writable,
	// no span: rawLen and idxReg name nothing).
	frame bool
	// global marks a package global's cell (`la` of a Function.Globals
	// name): writable, and accessed whole — at offset 0, at its width.
	global bool
	// table marks the whole of a constant data symbol (`la`): read-only,
	// its guarded elements derived like a frame array's.
	table bool
	// param marks the caller's copy of a by-reference record parameter
	// (or the result area) arriving in a contract register: the address
	// holds until the body writes that register, however many times a
	// later arm writes it — so it survives labels and calls on the path
	// before the write (forgetGuards).
	param bool
}

func checkRV64(fn *Function, decl *ast.FunctionStatement, symbols map[string]bool) []string {
	c := &rvChecker{fn: fn, symbols: symbols, bound: map[int]bool{}, clobbered: map[int]bool{}, written: map[int]bool{}, freed: map[int]bool{}, saved: map[int]*savedState{}, labelDisp: map[string]int64{}, labels: map[string]bool{}, spans: map[int]*rvSpan{}, writes: map[int]int{},
		fbound: map[int]bool{}, fclobbered: map[int]bool{}, fwritten: map[int]bool{}, ffreed: map[int]bool{}, fsaved: map[int]*savedState{},
		rem: map[int]rvRemFact{}, slack: map[int]rvSlackFact{}, gen: map[int]int{}, vclobbered: map[int]bool{}, vwritten: map[int]bool{}, frameAddrs: map[int]int64{}, lenAlias: map[int]int{}, rawDead: map[int]bool{}, composites: map[string]rvComposite{}, regions: map[int]rvRegion{}, resultChunks: 1}
	shared := &checker{fn: fn}
	shared.checkSignature(decl)
	if len(shared.errors) > 0 {
		return shared.errors
	}
	if fn.System {
		c.errorf(fn.Line, "the system capability is not admitted for rv64 units in this increment")
	}
	c.bindContract()
	if len(c.errors) > 0 {
		return c.errors
	}
	c.countWrites()
	c.forgetGuards()
	c.walk()
	for _, b := range fn.Bindings {
		if b.Register.Class == ClassRV64F {
			c.usesFloatFile = true
		}
	}
	if c.floatResult {
		c.usesFloatFile = true
	}
	fn.FloatFile = c.usesFloatFile
	fn.VectorFile = c.usesVectorFile
	return c.errors
}

func (c *rvChecker) errorf(line int, format string, args ...interface{}) {
	c.errors = append(c.errors, fmt.Sprintf("%s:%d: %s", c.fn.Name, line, fmt.Sprintf(format, args...)))
}

// bindContract assigns the LP64 registers and verifies every parameter
// is bound explicitly at its register.
func (c *rvChecker) bindContract() {
	sig := c.fn.Signature
	next := 10
	nextFloat := 10 // fa0–fa7
	expect := map[string]int{}
	expectLen := map[string]int{}
	expectFloat := map[string]int{}
	if sig.ReturnType != nil {
		if comp, isComposite := c.fn.Composites[typeText(sig.ReturnType)]; isComposite && comp.Size > 16 {
			// The caller's result area arrives in a0: the parameters follow.
			c.resultIndirect = true
			c.bound[10] = true
			c.regions[10] = rvRegion{size: comp.Size, writable: true, rawLen: -1, idxReg: -2, param: true}
			next = 11
		}
	}
	for _, param := range sig.Parameters {
		if comp, isComposite := c.fn.Composites[typeText(param.Type)]; isComposite {
			if comp.HFA {
				c.errorf(c.fn.Line, "parameter %s: %s carries floating-point fields (the hardware floating-point calling convention); the lane leaves it to the C backend", param.Name.Value, typeText(param.Type))
				continue
			}
			regs, indirect := 1, comp.Size > 16
			if !indirect {
				regs = int((comp.Size + 7) / 8)
			}
			if next+regs-1 > 17 {
				c.errorf(c.fn.Line, "record parameter %s needs %d registers; the integer register contract a0–a7 is exhausted", param.Name.Value, regs)
				continue
			}
			expect[param.Name.Value] = next
			c.composites[param.Name.Value] = rvComposite{reg: next, regs: regs, size: comp.Size, indirect: indirect}
			next += regs
			continue
		}
		if class, ok := contractClass(param.Type); ok && class == ClassV {
			// f32/f64 under LP64D: fa0–fa7 in declaration order, independent
			// of the integer registers (Oak.RiscV.lp64dBinding).
			if !strings.HasPrefix(typeText(param.Type), "simd.") {
				if nextFloat > 17 {
					c.errorf(c.fn.Line, "parameter %s: the floating-point register contract fa0–fa7 is exhausted", param.Name.Value)
					continue
				}
				expectFloat[param.Name.Value] = nextFloat
				nextFloat++
				continue
			}
		}
		if _, _, isSpan := spanShape(param.Type); isSpan {
			if next+1 > 17 {
				c.errorf(c.fn.Line, "span parameter %s needs two registers; the integer register contract a0–a7 is exhausted", param.Name.Value)
				continue
			}
			expect[param.Name.Value] = next
			expectLen[param.Name.Value] = next + 1
			next += 2
			continue
		}
		if class, ok := contractClass(param.Type); !ok || class == ClassV {
			c.errorf(c.fn.Line, "parameter %s has type %s, which the rv64 contract does not carry", param.Name.Value, typeText(param.Type))
			continue
		}
		if next > 17 {
			c.errorf(c.fn.Line, "parameter %s: the integer register contract a0–a7 is exhausted", param.Name.Value)
			continue
		}
		expect[param.Name.Value] = next
		next++
	}
	if sig.ReturnType != nil && typeText(sig.ReturnType) != "()" {
		if comp, isComposite := c.fn.Composites[typeText(sig.ReturnType)]; isComposite {
			switch {
			case comp.HFA:
				c.errorf(c.fn.Line, "result type %s carries floating-point fields (the hardware floating-point calling convention); the lane leaves it to the C backend", typeText(sig.ReturnType))
			case c.resultIndirect:
			default:
				c.hasResult = true
				c.resultChunks = int((comp.Size + 7) / 8)
			}
		} else if typeText(sig.ReturnType) == "never" {
			c.never = true
		} else if class, ok := contractClass(sig.ReturnType); ok && class == ClassV && !strings.HasPrefix(typeText(sig.ReturnType), "simd.") {
			c.floatResult = true // f32/f64 in fa0
		} else if !ok || class == ClassV {
			c.errorf(c.fn.Line, "result type %s is not carried by the rv64 contract", typeText(sig.ReturnType))
		} else {
			c.hasResult = true
		}
	}
	seen := map[string]bool{}
	for _, b := range c.fn.Bindings {
		want, declared := expect[b.Param]
		if _, isFloat := expectFloat[b.Param]; !declared && !isFloat {
			c.errorf(b.Line, "bind names %s, which is not a parameter", b.Param)
			continue
		}
		if seen[b.Param] {
			c.errorf(b.Line, "parameter %s is bound twice", b.Param)
			continue
		}
		seen[b.Param] = true
		if freg, isFloat := expectFloat[b.Param]; isFloat {
			if b.Register.Class != ClassRV64F || b.Register.Num != freg || b.Length != nil {
				c.errorf(b.Line, "parameter %s must be bound to %s (its LP64D contract register), not %s", b.Param, rv64FloatRegisterName(freg), b.Register.Text)
				continue
			}
			c.fbound[freg] = true
			continue
		}
		if b.Register.Class != ClassRV64X || b.Register.Num != want {
			c.errorf(b.Line, "parameter %s must be bound to %s (its LP64 contract register), not %s", b.Param, rv64RegisterName(want), b.Register.Text)
			continue
		}
		if comp, isComposite := c.composites[b.Param]; isComposite {
			switch {
			case comp.regs == 2 && (b.Length == nil || b.Length.Class != ClassRV64X || b.Length.Num != comp.reg+1):
				c.errorf(b.Line, "record parameter %s (%d bytes) arrives as two chunks: bind %s, %s = %s", b.Param, comp.size, rv64RegisterName(comp.reg), rv64RegisterName(comp.reg+1), b.Param)
				continue
			case comp.regs == 1 && b.Length != nil:
				c.errorf(b.Line, "record parameter %s (%d bytes) arrives in %s alone", b.Param, comp.size, rv64RegisterName(comp.reg))
				continue
			}
			for i := 0; i < comp.regs; i++ {
				c.bound[comp.reg+i] = true
			}
			if comp.indirect {
				// The caller's copy: readable at constant offsets inside it.
				c.regions[comp.reg] = rvRegion{size: comp.size, rawLen: -1, idxReg: -2, param: true}
			}
			continue
		}
		if lenReg, isSpan := expectLen[b.Param]; isSpan {
			if b.Length == nil || b.Length.Class != ClassRV64X || b.Length.Num != lenReg {
				c.errorf(b.Line, "span parameter %s binds its {base, len} pair as `bind %s, %s = %s`", b.Param, rv64RegisterName(want), rv64RegisterName(lenReg), b.Param)
				continue
			}
			c.bound[lenReg] = true
			elem, writable, _ := spanShape(sigParamType(sig, b.Param))
			c.spans[want] = &rvSpan{rawLen: lenReg, elem: elem, writable: writable}
		} else if b.Length != nil {
			c.errorf(b.Line, "parameter %s is not a span; bind one register", b.Param)
			continue
		}
		c.bound[want] = true
	}
	for name, reg := range expect {
		if !seen[name] {
			c.errorf(c.fn.Line, "parameter %s is not bound (`bind %s = %s`)", name, rv64RegisterName(reg), name)
		}
	}
	for name, reg := range expectFloat {
		if !seen[name] {
			c.errorf(c.fn.Line, "parameter %s is not bound (`bind %s = %s`)", name, rv64FloatRegisterName(reg), name)
		}
	}
	for _, reg := range c.fn.Clobbers {
		if reg.Class == ClassRV64V {
			// Every vector register is caller-saved under the psABI: all
			// are clobberable, none carries a save obligation.
			c.vclobbered[reg.Num] = true
			continue
		}
		if reg.Class == ClassRV64F {
			if rv64FloatCalleeSaved(reg.Num) {
				c.errorf(c.fn.Line, "%s is callee-saved (fs0–fs11): save it to the frame (fsd) and restore it before ret instead of clobbering it", reg.Text)
				continue
			}
			c.fclobbered[reg.Num] = true
			continue
		}
		switch {
		case reg.Class == ClassSP:
			c.errorf(c.fn.Line, "sp cannot be a clobber; the frame directive governs it")
		case reg.Class != ClassRV64X:
			c.errorf(c.fn.Line, "clobber %s is not an rv64 general register", reg.Text)
		case reg.Num == 0:
			c.errorf(c.fn.Line, "zero cannot be clobbered")
		case reg.Num == 1:
			c.errorf(c.fn.Line, "ra is the return address: save it to the frame and restore it before ret instead of clobbering it")
		case reg.Num == 3 || reg.Num == 4:
			c.errorf(c.fn.Line, "%s is the platform's (gp/tp); it cannot be clobbered", reg.Text)
		case rv64CalleeSaved(reg.Num):
			c.errorf(c.fn.Line, "%s is callee-saved (s0–s11): save it to the frame and restore it before ret instead of clobbering it", reg.Text)
		default:
			c.clobbered[reg.Num] = true
		}
	}
}

// preserved reports the registers under the save/restore obligation: ra
// and s0–s11.
func rv64Preserved(num int) bool { return num == 1 || rv64CalleeSaved(num) }

func (c *rvChecker) readable(reg Register) bool {
	if reg.Class == ClassSP {
		return true
	}
	if reg.Class == ClassRV64F {
		num := reg.Num
		if rv64FloatCalleeSaved(num) {
			state := c.fsaved[num]
			return state == nil || !state.written || c.fwritten[num]
		}
		return c.fbound[num] || c.fwritten[num]
	}
	if reg.Class == ClassRV64V {
		return c.vwritten[reg.Num]
	}
	if reg.Class != ClassRV64X {
		return false
	}
	num := reg.Num
	if rv64Preserved(num) {
		// The caller's value is readable until a write; after a write it is
		// this function's, readable as written.
		state := c.saved[num]
		return state == nil || !state.written || c.written[num]
	}
	return num == 0 || c.bound[num] || c.written[num]
}

func (c *rvChecker) read(reg Register, line int) {
	if !c.readable(reg) {
		c.errorf(line, "read of %s, which is neither bound nor written", reg.Text)
	}
}

// write records a write to reg when it is admitted: bound, the result
// register a0, a declared clobber, a caller-saved register released by a
// call, or a preserved register already saved to the frame.
func (c *rvChecker) write(reg Register, line int) {
	if reg.Class == ClassSP {
		c.errorf(line, "sp is written only by `addi sp, sp, imm`")
		return
	}
	if reg.Class == ClassRV64F {
		c.usesFloatFile = true
		num := reg.Num
		switch {
		case num == 10 && c.floatResult, c.fbound[num], c.fclobbered[num], c.ffreed[num]:
			c.fwritten[num] = true
		case rv64FloatCalleeSaved(num):
			state := c.fsaved[num]
			if !state.saved {
				c.errorf(line, "%s is callee-saved (fs0–fs11): save it to the frame (`fsd %s, imm(sp)`) before writing it", reg.Text, reg.Text)
				return
			}
			state.written = true
			state.restored = false
			c.fwritten[num] = true
		default:
			c.errorf(line, "write to %s, which is neither bound, the result register fa0, nor a declared clobber", reg.Text)
		}
		return
	}
	if reg.Class == ClassRV64V {
		c.usesVectorFile = true
		if !c.vclobbered[reg.Num] {
			c.errorf(line, "write to %s, which is not a declared clobber (vector registers are caller-saved: `clobber %s`)", reg.Text, reg.Text)
			return
		}
		c.vwritten[reg.Num] = true
		return
	}
	if reg.Class != ClassRV64X {
		return
	}
	num := reg.Num
	if num != 0 {
		c.forgetRegister(num)
	}
	switch {
	case num == 0:
		return // a write to zero is discarded
	case num == 10 && c.hasResult, num == 11 && c.hasResult && c.resultChunks == 2, c.bound[num], c.clobbered[num], c.freed[num]:
		c.written[num] = true
	case rv64Preserved(num):
		state := c.saved[num]
		if !state.saved {
			what := "callee-saved (s0–s11)"
			if num == 1 {
				what = "the return address"
			}
			c.errorf(line, "%s is %s: save it to the frame (`sd %s, imm(sp)`) before writing it", reg.Text, what, reg.Text)
			return
		}
		state.written = true
		state.restored = false
		c.written[num] = true
	default:
		c.errorf(line, "write to %s, which is neither bound, the result register a0, nor a declared clobber", reg.Text)
	}
}

func (c *rvChecker) walk() {
	for _, item := range c.fn.Items {
		if label, ok := item.(Label); ok {
			if c.labels[label.Name] {
				c.errorf(label.Line, "duplicate label %s", label.Name)
			}
			c.labels[label.Name] = true
		}
	}
	for num := 0; num < 32; num++ {
		if rv64Preserved(num) {
			c.saved[num] = &savedState{}
		}
		if rv64FloatCalleeSaved(num) {
			c.fsaved[num] = &savedState{}
		}
	}
	terminated := false
	for _, item := range c.fn.Items {
		switch it := item.(type) {
		case Label:
			c.enterLabel(it)
			terminated = false
		case Align:
			c.errorf(it.Line, "align regions are not admitted for rv64 units in this increment")
		case Instruction:
			if c.unreachable {
				c.errorf(it.Line, "unreachable instruction after an unconditional transfer; start a label")
				c.unreachable = false
			}
			terminated = c.instruction(it)
		}
	}
	if !terminated && !c.unreachable {
		c.errorf(c.fn.Line, "the body falls through its end; finish with ret or a jump")
	}
}

// countWrites counts, over the whole body, the instructions writing each
// register: a register written by exactly one instruction holds the same
// value on every path that defined it, so a fact about it (a normalized
// length, a constant) survives a label; every other fact is a guard fact
// and is forgotten where paths meet.
func (c *rvChecker) countWrites() {
	var instrs []Instruction
	for _, item := range c.fn.Items {
		if instr, isInstr := item.(Instruction); isInstr {
			instrs = append(instrs, rv64Base(instr))
		}
	}
	// Raw length registers and their straight-line copies (`mv rD, aL`),
	// read in order: the normalization pair may read a copy.
	rawLens := map[int]bool{}
	for _, span := range c.spans {
		rawLens[span.rawLen] = true
	}
	for _, base := range instrs {
		if base.Mnemonic == "addi" && len(base.Operands) == 3 {
			dest, okD := base.Operands[0].(Register)
			src, okS := base.Operands[1].(Register)
			if okD && okS && dest.Class == ClassRV64X && src.Class == ClassRV64X && base.Operands[2].(Immediate).Value == 0 && rawLens[src.Num] {
				rawLens[dest.Num] = true
			}
		}
	}
	for i, base := range instrs {
		if len(base.Operands) == 0 || rv64Branches[base.Mnemonic] || rv64Stores[base.Mnemonic] != 0 || base.Mnemonic == "call" {
			continue
		}
		dest, isReg := base.Operands[0].(Register)
		if !isReg || dest.Class != ClassRV64X {
			continue
		}
		// The normalization pair `slli rX, len, 32; srli rX, rX, 32` is one
		// definition of rX: its second half counts with its first.
		if base.Mnemonic == "srli" && i > 0 && isNormalization(instrs[i-1], base, rawLens) {
			continue
		}
		// A preserved register's restore from the frame (`ld sK, imm(sp)`)
		// is not a definition the body reads: its facts are forgotten at
		// the restore itself.
		if base.Mnemonic == "ld" && rv64Preserved(dest.Num) {
			if mem, isMem := base.Operands[1].(Memory); isMem && mem.Base.Class == ClassSP {
				continue
			}
		}
		c.writes[dest.Num]++
	}
}

// isNormalization recognizes `slli rX, len, 32` followed by `srli rX, rX, 32`
// over a span's raw length register or a copy of one.
func isNormalization(first, second Instruction, rawLens map[int]bool) bool {
	if first.Mnemonic != "slli" || second.Mnemonic != "srli" || len(first.Operands) != 3 || len(second.Operands) != 3 {
		return false
	}
	d1, s1, i1 := first.Operands[0].(Register), first.Operands[1].(Register), first.Operands[2].(Immediate)
	d2, s2, i2 := second.Operands[0].(Register), second.Operands[1].(Register), second.Operands[2].(Immediate)
	if i1.Value != 32 || i2.Value != 32 || d1.Num != d2.Num || s2.Num != d2.Num {
		return false
	}
	return rawLens[s1.Num]
}

// stable reports a register written by at most one instruction in the body.
func (c *rvChecker) stable(num int) bool { return c.writes[num] <= 1 }

// forgetGuards drops the guard facts where paths meet (a label) or after a
// call: index bounds, scaled indices, element regions, minimum lengths.
// Normalized lengths, half-normalizations, and constants held by stable
// registers survive (countWrites).
func (c *rvChecker) forgetGuards() {
	// A normalized (or half-normalized) copy holds the length of the span
	// it names whatever happens to the raw register afterwards: only the
	// copy's own register must be written once.
	keepInt := func(m map[int]int) map[int]int {
		out := map[int]int{}
		for reg, src := range m {
			if c.stable(reg) {
				out[reg] = src
			}
		}
		return out
	}
	c.shl32 = keepInt(c.shl32)
	c.lenNorm = keepInt(c.lenNorm)
	lenAlias := map[int]int{}
	for reg, raw := range c.lenAlias {
		if c.stable(reg) {
			lenAlias[reg] = raw
		}
	}
	c.lenAlias = lenAlias
	consts := map[int]int64{}
	for reg, k := range c.consts {
		if c.stable(reg) {
			consts[reg] = k
		}
	}
	c.consts = consts
	frameAddrs := map[int]int64{}
	for reg, addr := range c.frameAddrs {
		if c.stable(reg) {
			frameAddrs[reg] = addr
		}
	}
	c.frameAddrs = frameAddrs
	c.idx = map[int]rvIndexFact{}
	c.scaled = map[int]rvScaledFact{}
	// A region in a register written once holds one fixed address (the
	// caller's record or result area parked in a callee-saved register):
	// it survives labels and calls.
	regions := map[int]rvRegion{}
	for reg, region := range c.regions {
		if c.stable(reg) || (region.param && !c.written[reg]) {
			regions[reg] = region
		}
	}
	c.regions = regions
	c.rem = map[int]rvRemFact{}
	c.slack = map[int]rvSlackFact{}
	c.vcfg = nil
	for _, span := range c.spans {
		span.hasMin = false
	}
}

// forgetRegister drops the facts a write to num invalidates: what num
// held, and what was derived from it.
func (c *rvChecker) forgetRegister(num int) {
	c.gen[num]++
	delete(c.rem, num)
	for reg, fact := range c.rem {
		if fact.lenReg == num || fact.idxReg == num {
			delete(c.rem, reg)
		}
	}
	delete(c.shl32, num)
	delete(c.lenNorm, num)
	delete(c.consts, num)
	delete(c.idx, num)
	delete(c.scaled, num)
	delete(c.regions, num)
	delete(c.frameAddrs, num)
	delete(c.lenAlias, num)
	delete(c.slack, num)
	for reg, fact := range c.slack {
		if fact.lenReg == num {
			delete(c.slack, reg)
		}
	}
	for reg, fact := range c.idx {
		if fact.lenReg == num {
			delete(c.idx, reg)
		}
	}
	for reg, fact := range c.scaled {
		if fact.guard.lenReg == num {
			delete(c.scaled, reg)
		}
	}
	// A normalized or half-normalized copy names its span by the bound raw
	// length register; the name outlives the register's value (the length
	// of a span never changes), so those facts stay. The register itself
	// normalizes nothing further.
	delete(c.spans, num)
	for _, span := range c.spans {
		if span.rawLen == num {
			span.hasMin = false
			c.rawDead[num] = true
		}
	}
}

// enterLabel merges control at a label: its sp displacement must agree
// with every branch that targets it and with the fall-through path when
// one reaches it. After an unconditional transfer no path falls through,
// so the displacement is the branches' (the trap block after `ret`); a
// label reachable only by a later branch has no known displacement and is
// refused, as the AArch64 checker refuses it.
func (c *rvChecker) enterLabel(label Label) {
	c.forgetGuards()
	known, has := c.labelDisp[label.Name]
	switch {
	case has && !c.unreachable && known != c.disp:
		c.errorf(label.Line, "sp displacement %d at label %s disagrees with %d on another path", c.disp, label.Name, known)
	case has:
		c.disp = known
	case c.unreachable:
		c.errorf(label.Line, "label %s has no known stack displacement: it is only reachable by a later branch", label.Name)
	}
	c.unreachable = false
	c.labelDisp[label.Name] = c.disp
}

func (c *rvChecker) branchTo(name string, line int) {
	if !c.labels[name] {
		c.errorf(line, "branch to unknown label %s", name)
		return
	}
	if known, has := c.labelDisp[name]; has {
		if known != c.disp {
			c.errorf(line, "branch to %s with sp displacement %d, but the label has %d", name, c.disp, known)
		}
		return
	}
	c.labelDisp[name] = c.disp
}

// frameAddress checks an `imm(sp)` access of width bytes and returns its
// entry-relative address.
func (c *rvChecker) frameAddress(mem Memory, width int64, line int) (int64, bool) {
	if mem.Base.Class != ClassSP {
		c.errorf(line, "memory through %s: only the sp frame is admitted for rv64 units in this increment", mem.Base.Text)
		return 0, false
	}
	if c.fn.Frame == 0 {
		c.errorf(line, "memory access without a frame directive")
		return 0, false
	}
	addr := -c.disp + mem.Offset
	if addr < -c.fn.Frame || addr+width > 0 {
		c.errorf(line, "frame access at entry-relative %d..%d is outside the declared frame [-%d, 0)", addr, addr+width, c.fn.Frame)
		return 0, false
	}
	if addr%width != 0 {
		c.errorf(line, "frame access at %d is not aligned to its %d-byte width", addr, width)
		return 0, false
	}
	return addr, true
}

// call records a transfer that writes ra and returns: ra must be saved
// already; the caller-saved registers are released.
func (c *rvChecker) call(target string, line int) {
	if !c.saved[1].saved {
		c.errorf(line, "a call overwrites ra: save it to the frame (`sd ra, imm(sp)`) first and restore it before ret")
	}
	if target != "" && !c.labels[target] && !c.symbols[target] {
		c.errorf(line, "call to unknown symbol %s", target)
	}
	c.saved[1].written = true
	c.saved[1].restored = false
	c.forgetGuards()
	// vl, vtype, and every vector register are not preserved across a call.
	c.vwritten = map[int]bool{}
	for num := 0; num <= 31; num++ {
		if !rv64FloatCalleeSaved(num) {
			delete(c.fwritten, num)
			delete(c.fbound, num)
			c.ffreed[num] = true
		}
	}
	// The callee's floating-point result is readable in fa0, as its integer
	// result is in a0: the checker sees no callee signature, so it gives
	// the two result registers the same latitude (the AArch64 checker's v0).
	c.fwritten[10] = true
	for num := 5; num <= 31; num++ {
		if num >= 5 && num <= 7 || num >= 10 && num <= 17 || num >= 28 {
			delete(c.written, num)
			delete(c.bound, num)
			c.freed[num] = true
			// A span pair or a length copy parked there does not survive
			// the callee: only the callee-saved copies do.
			c.forgetRegister(num)
		}
	}
	c.written[10] = true // the callee's result
	if c.fn.TwoChunkResults[target] {
		c.written[11] = true // its second chunk: the callee returns a two-chunk record
	}
}

// instruction checks one instruction; true when it ends the path.
func (c *rvChecker) instruction(instr Instruction) bool {
	line := instr.Line
	base := rv64Base(instr)
	name := base.Mnemonic
	ops := base.Operands
	reg := func(i int) Register { return ops[i].(Register) }
	if shape, isVector := rv64VectorShapes[name]; isVector {
		return c.vectorInstruction(base, shape, line)
	}
	if rv64Branches[name] {
		c.read(reg(0), line)
		c.read(reg(1), line)
		c.branchTo(ops[2].(Symbol).Name, line)
		c.guardFacts(name, reg(0), reg(1))
		return false
	}
	switch name {
	case "jal":
		target := ops[1].(Symbol).Name
		if reg(0).Num == 0 {
			c.branchTo(target, line)
			c.unreachable = true
			return true
		}
		if reg(0).Num != 1 {
			c.errorf(line, "jal links only through ra")
			return false
		}
		c.call(target, line)
		return false
	case "call":
		c.call(ops[0].(Symbol).Name, line)
		return false
	case "auipc":
		c.write(reg(0), line)
		return false
	case "la":
		// The address of a constant data symbol: a read-only region of its
		// size, written once so it survives labels (stable).
		sym, isSym := ops[1].(Symbol)
		if !isSym {
			c.errorf(line, "la takes a data symbol")
			return false
		}
		if global, isGlobal := c.fn.Globals[sym.Name]; isGlobal {
			// A package global's cell (docs/spec/94-assembler.md §9).
			c.write(reg(0), line)
			c.regions[reg(0).Num] = rvRegion{size: int64(global.Bits / 8), writable: true, rawLen: -1, idxReg: -2, global: true}
			return false
		}
		size, known := c.fn.Tables[sym.Name]
		if !known {
			c.errorf(line, "la %s: not a constant data symbol or global of the program", sym.Name)
			return false
		}
		c.write(reg(0), line)
		c.regions[reg(0).Num] = rvRegion{size: size, rawLen: -1, idxReg: -2, table: true}
		return false
	case "li":
		imm := ops[1].(Immediate).Value
		if imm < -(1<<31) || imm >= 1<<31 {
			c.errorf(line, "li admits 32-bit immediates in this increment (%d)", imm)
		}
		c.write(reg(0), line)
		if reg(0).Class == ClassRV64X && imm >= 0 {
			c.consts[reg(0).Num] = imm
		}
		return false
	case "jalr":
		mem := ops[1].(Memory)
		if reg(0).Num == 0 && mem.Base.Class == ClassRV64X && mem.Base.Num == 1 && mem.Offset == 0 {
			return c.ret(line)
		}
		c.read(mem.Base, line)
		if reg(0).Num == 0 {
			// jr: an indirect jump out of the function.
			if c.disp != 0 {
				c.errorf(line, "indirect jump with sp displacement %d", c.disp)
			}
			c.unreachable = true
			return true
		}
		if reg(0).Num != 1 {
			c.errorf(line, "jalr links only through ra")
			return false
		}
		c.call("", line)
		return false
	case "addi":
		if reg(0).Class == ClassSP {
			if reg(1).Class != ClassSP {
				c.errorf(line, "sp may only be moved by `addi sp, sp, imm`")
				return false
			}
			imm := ops[2].(Immediate).Value
			if imm%16 != 0 {
				c.errorf(line, "sp moves by %d, which is not a multiple of 16", imm)
				return false
			}
			next := c.disp - imm
			if next < 0 || next > c.fn.Frame {
				c.errorf(line, "sp displacement %d leaves the declared frame [0, %d]", next, c.fn.Frame)
				return false
			}
			c.disp = next
			return false
		}
	case "lui":
		imm := ops[1].(Immediate).Value
		if imm < -(1<<19) || imm > (1<<20)-1 {
			c.errorf(line, "lui immediate %d is outside the 20-bit range", imm)
		}
		c.write(reg(0), line)
		return false
	case "ebreak":
		// A trap: the failure arm of a guard. The path ends here.
		c.unreachable = true
		return true
	case "ecall", "fence":
		c.errorf(line, "%s is outside the rv64 subset of this increment", name)
		return false
	}
	if width, isLoad := rv64FloatLoads[name]; isLoad {
		mem := ops[1].(Memory)
		dest := reg(0)
		if mem.Base.Class != ClassSP {
			// A float element of a span or an owned array: the same guarded
			// region an integer load goes through.
			c.read(mem.Base, line)
			c.spanAccess(mem, int64(width), false, line)
			c.write(dest, line)
			return false
		}
		addr, ok := c.frameAddress(mem, int64(width), line)
		if ok && rv64FloatCalleeSaved(dest.Num) {
			state := c.fsaved[dest.Num]
			if state.saved && width == 8 && state.slot == addr {
				state.restored = true
				state.written = false
				delete(c.fwritten, dest.Num)
				return false
			}
			if state.saved {
				c.errorf(line, "%s is restored from entry-relative %d, but was saved at %d", dest.Text, addr, state.slot)
				return false
			}
		}
		c.write(dest, line)
		return false
	}
	if width, isStore := rv64FloatStores[name]; isStore {
		mem := ops[1].(Memory)
		src := reg(0)
		c.read(src, line)
		if mem.Base.Class != ClassSP {
			c.read(mem.Base, line)
			c.spanAccess(mem, int64(width), true, line)
			return false
		}
		addr, ok := c.frameAddress(mem, int64(width), line)
		if ok && rv64FloatCalleeSaved(src.Num) && width == 8 {
			state := c.fsaved[src.Num]
			if !state.saved && !state.written {
				state.saved, state.slot = true, addr
			}
		}
		return false
	}
	if shape, isFloat := rv64FloatShapes[name]; isFloat {
		// Destination first, sources after; a trailing rounding mode reads
		// nothing. Comparisons and integer conversions write an x register.
		c.usesFloatFile = true
		required := strings.TrimSuffix(shape, "r")
		for i := 1; i < len(required); i++ {
			c.read(reg(i), line)
		}
		c.write(reg(0), line)
		return false
	}
	if width, isLoad := rv64Loads[name]; isLoad {
		mem := ops[1].(Memory)
		if mem.Base.Class != ClassSP {
			c.read(mem.Base, line)
			c.spanAccess(mem, int64(width), false, line)
			c.write(reg(0), line)
			return false
		}
		addr, ok := c.frameAddress(mem, int64(width), line)
		dest := reg(0)
		if ok && dest.Class == ClassRV64X && rv64Preserved(dest.Num) {
			state := c.saved[dest.Num]
			if state.saved && width == 8 && state.slot == addr {
				// The restore: the caller's value is back, and no fact about
				// the value this function held there survives.
				state.restored = true
				state.written = false
				delete(c.written, dest.Num)
				c.forgetRegister(dest.Num)
				return false
			}
			if state.saved {
				c.errorf(line, "%s is restored from entry-relative %d, but was saved at %d", dest.Text, addr, state.slot)
				return false
			}
		}
		c.write(dest, line)
		return false
	}
	if width, isStore := rv64Stores[name]; isStore {
		mem := ops[1].(Memory)
		src := reg(0)
		c.read(src, line)
		if mem.Base.Class != ClassSP {
			c.read(mem.Base, line)
			c.spanAccess(mem, int64(width), true, line)
			return false
		}
		addr, ok := c.frameAddress(mem, int64(width), line)
		if ok && src.Class == ClassRV64X && rv64Preserved(src.Num) && width == 8 {
			state := c.saved[src.Num]
			if !state.saved && !state.written {
				state.saved, state.slot = true, addr
			}
		}
		return false
	}
	switch name {
	case "add", "sub", "and", "or", "xor", "sll", "srl", "sra", "slt", "sltu", "addw", "subw", "sllw", "srlw", "sraw",
		"mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu", "mulw", "divw", "divuw", "remw", "remuw":
		c.read(reg(1), line)
		c.read(reg(2), line)
		// The facts an `add` derives come from its sources as they were
		// before the destination is written (dest may be a source).
		pre := c.snapshot()
		c.write(reg(0), line)
		if name == "add" {
			pre.deriveRegion(c, reg(0), reg(1), reg(2))
		}
		if name == "sub" {
			pre.deriveRemaining(c, reg(0), reg(1), reg(2))
			if k, isConst := pre.consts[reg(2).Num]; isConst {
				pre.deriveSlack(c, reg(0), reg(1), k)
			}
		}
		return false
	case "addi", "andi", "ori", "xori", "slti", "sltiu", "slli", "srli", "srai", "addiw", "slliw", "srliw", "sraiw":
		imm := ops[2].(Immediate).Value
		switch name {
		case "slli", "srli", "srai":
			if imm < 0 || imm > 63 {
				c.errorf(line, "shift amount %d is outside 0..63", imm)
			}
		case "slliw", "srliw", "sraiw":
			if imm < 0 || imm > 31 {
				c.errorf(line, "shift amount %d is outside 0..31", imm)
			}
		default:
			if imm < -2048 || imm > 2047 {
				c.errorf(line, "immediate %d is outside the 12-bit signed range", imm)
			}
		}
		c.read(reg(1), line)
		pre := c.snapshot()
		c.write(reg(0), line)
		pre.deriveShift(c, name, reg(0), reg(1), imm)
		if name == "addi" && imm < 0 {
			pre.deriveSlack(c, reg(0), reg(1), -imm)
		}
		if name == "addi" && reg(1).Class == ClassSP && reg(0).Class == ClassRV64X && reg(0).Num != 0 {
			// `addi rD, sp, imm`: rD holds a frame address (an owned array's
			// base, docs/spec/94-assembler.md §9), entry-relative.
			if addr := -c.disp + imm; addr >= -c.fn.Frame && addr <= 0 {
				c.frameAddrs[reg(0).Num] = addr
			}
		}
		return false
	}
	c.errorf(line, "instruction %s is not admitted by the RV64 checker", instr.Mnemonic)
	return false
}

// ret checks the return: displacement 0, every written preserved register
// restored, the result written.
func (c *rvChecker) ret(line int) bool {
	if c.never {
		c.errorf(line, "ret from a never-returning function")
	}
	if c.disp != 0 {
		c.errorf(line, "ret with sp displacement %d; release the frame first", c.disp)
	}
	for num := 0; num < 32; num++ {
		state := c.saved[num]
		if state != nil && state.written && !state.restored {
			c.errorf(line, "ret with %s written but not restored from its frame slot", rv64RegisterName(num))
		}
	}
	if c.hasResult && !c.written[10] && !c.bound[10] {
		c.errorf(line, "ret without writing the result register a0")
	}
	if c.hasResult && c.resultChunks == 2 && !c.written[11] && !c.bound[11] {
		c.errorf(line, "ret without writing the result's second chunk a1")
	}
	for num := 0; num < 32; num++ {
		state := c.fsaved[num]
		if state != nil && state.written && !state.restored {
			c.errorf(line, "ret with %s written but not restored from its frame slot", rv64FloatRegisterName(num))
		}
	}
	if c.floatResult && !c.fwritten[10] && !c.fbound[10] {
		c.errorf(line, "ret without writing the result register fa0")
	}
	c.unreachable = true
	return true
}

// guardFacts records what the fall-through of a conditional branch proves
// (Oak.RiscV.index_guard): `bgeu idx, len, L` — idx < len when len is a
// normalized length register or a constant register; `bltu len, K, L` —
// len >= K for the span whose normalized length is len.
func (c *rvChecker) guardFacts(name string, left, right Register) {
	if left.Class != ClassRV64X || right.Class != ClassRV64X {
		return
	}
	switch name {
	case "bgeu":
		if _, isLen := c.lenNorm[right.Num]; isLen {
			c.idx[left.Num] = rvIndexFact{lenReg: right.Num}
			return
		}
		if k, isConst := c.consts[right.Num]; isConst && k > 0 {
			c.idx[left.Num] = rvIndexFact{lenReg: -1, bound: k}
		}
	case "bltu":
		if slack, isSlack := c.slack[left.Num]; isSlack {
			// `bltu t, idx, trap` with t = len - K: the fall-through knows
			// idx <= len - K, so idx + K <= len (Oak.RiscV.slack_guard).
			if right.Num != 0 {
				c.idx[right.Num] = rvIndexFact{lenReg: slack.lenReg, slack: slack.k}
			}
			return
		}
		raw, isLen := c.lenNorm[left.Num]
		k, isConst := c.consts[right.Num]
		if !isLen || !isConst || k <= 0 {
			return
		}
		for _, span := range c.spans {
			if span.rawLen == raw {
				span.hasMin = true
				span.minLen = k
			}
		}
	}
}

// rvSnapshot is the guard state before an instruction writes its
// destination: the facts of the sources, read before the write forgets
// them (the destination may be one of the sources).
type rvSnapshot struct {
	shl32      map[int]int
	lenNorm    map[int]int
	consts     map[int]int64
	idx        map[int]rvIndexFact
	scaled     map[int]rvScaledFact
	spans      map[int]*rvSpan
	gen        map[int]int
	frameAddrs map[int]int64
	lenAlias   map[int]int
	rawDead    map[int]bool
	regions    map[int]rvRegion
}

func (c *rvChecker) snapshot() rvSnapshot {
	copyInt := func(m map[int]int) map[int]int {
		out := make(map[int]int, len(m))
		for k, v := range m {
			out[k] = v
		}
		return out
	}
	consts := make(map[int]int64, len(c.consts))
	for k, v := range c.consts {
		consts[k] = v
	}
	idx := make(map[int]rvIndexFact, len(c.idx))
	for k, v := range c.idx {
		idx[k] = v
	}
	scaled := make(map[int]rvScaledFact, len(c.scaled))
	for k, v := range c.scaled {
		scaled[k] = v
	}
	spans := make(map[int]*rvSpan, len(c.spans))
	for k, v := range c.spans {
		copied := *v
		spans[k] = &copied
	}
	frameAddrs := make(map[int]int64, len(c.frameAddrs))
	for k, v := range c.frameAddrs {
		frameAddrs[k] = v
	}
	rawDead := make(map[int]bool, len(c.rawDead))
	for k, v := range c.rawDead {
		rawDead[k] = v
	}
	regions := make(map[int]rvRegion, len(c.regions))
	for k, v := range c.regions {
		regions[k] = v
	}
	return rvSnapshot{shl32: copyInt(c.shl32), lenNorm: copyInt(c.lenNorm), consts: consts, idx: idx, scaled: scaled, spans: spans, gen: copyInt(c.gen), frameAddrs: frameAddrs, lenAlias: copyInt(c.lenAlias), rawDead: rawDead, regions: regions}
}

// rawLen reports a register holding a span's raw length: the bound
// register, or a copy of it.
func (pre rvSnapshot) rawLen(num int) bool {
	if _, isAlias := pre.lenAlias[num]; isAlias {
		return true
	}
	if pre.rawDead[num] {
		return false
	}
	for _, span := range pre.spans {
		if span.rawLen == num {
			return true
		}
	}
	return false
}

// canonicalRaw names the bound raw length register a register stands for.
func (pre rvSnapshot) canonicalRaw(num int) int {
	if raw, isAlias := pre.lenAlias[num]; isAlias {
		return raw
	}
	return num
}

// deriveShift records the shift facts: `slli rX, len, 32` then
// `srli rX, rX, 32` normalizes a raw length register; `slli t, idx, s`
// scales an index; `addi rD, rS, 0` (mv) copies a normalized length or a
// constant.
func (pre rvSnapshot) deriveShift(c *rvChecker, name string, dest, src Register, imm int64) {
	if dest.Class != ClassRV64X || src.Class != ClassRV64X || dest.Num == 0 {
		return
	}
	switch name {
	case "slli":
		if imm == 32 && pre.rawLen(src.Num) {
			c.shl32[dest.Num] = pre.canonicalRaw(src.Num)
			return
		}
		if guard, guarded := pre.idx[src.Num]; guarded && imm >= 0 && imm < 32 {
			c.scaled[dest.Num] = rvScaledFact{guard: guard, shift: int(imm), idxReg: src.Num, idxGen: pre.gen[src.Num]}
		}
	case "srli":
		if raw, half := pre.shl32[src.Num]; half && imm == 32 {
			c.lenNorm[dest.Num] = raw
		}
	case "addi":
		if src.Num == 0 {
			// li with a 12-bit immediate is addi from zero: a constant.
			if imm >= 0 {
				c.consts[dest.Num] = imm
			}
			return
		}
		if imm == 0 {
			if raw, isLen := pre.lenNorm[src.Num]; isLen {
				c.lenNorm[dest.Num] = raw
			}
			if k, isConst := pre.consts[src.Num]; isConst {
				c.consts[dest.Num] = k
			}
			// A span's pair parked (or passed on): the copy of the base is a
			// base of the same span, the copy of the length a raw length.
			if span, isBase := pre.spans[src.Num]; isBase && dest.Num != src.Num {
				copied := *span
				c.spans[dest.Num] = &copied
			}
			if pre.rawLen(src.Num) && dest.Num != src.Num {
				c.lenAlias[dest.Num] = pre.canonicalRaw(src.Num)
			}
			// A record's address parked: the copy addresses the same region.
			if region, isRegion := pre.regions[src.Num]; isRegion && dest.Num != src.Num {
				c.regions[dest.Num] = region
			}
		}
	}
}

// deriveRegion records `add rD, base, t` as the address of one element of
// the span at base when t = idx << s, idx is guarded below the span's
// length (or below a constant its proven minimum covers), and 2^s is the
// element size (Oak.RiscV.index_guard).
func (pre rvSnapshot) deriveRegion(c *rvChecker, dest, left, right Register) {
	if dest.Class != ClassRV64X || left.Class != ClassRV64X || right.Class != ClassRV64X {
		return
	}
	base, offset := left, right
	span, isBase := pre.spans[base.Num]
	if !isBase {
		base, offset = right, left
		span, isBase = pre.spans[base.Num]
	}
	if !isBase {
		pre.deriveFrameRegion(c, dest, left, right)
		return
	}
	if dest.Num == base.Num {
		return
	}
	guard, guarded := pre.idx[offset.Num]
	shift := 0
	idxReg, idxGen := offset.Num, pre.gen[offset.Num]
	if scale, isScaled := pre.scaled[offset.Num]; isScaled {
		guard, guarded, shift = scale.guard, true, scale.shift
		idxReg, idxGen = scale.idxReg, scale.idxGen
	}
	if !guarded || int64(1)<<uint(shift) != span.elem {
		return
	}
	if guard.lenReg < 0 {
		idxReg = -2 // a constant bound: no `len - idx` can name it
	}
	inBounds := (guard.lenReg >= 0 && pre.lenNorm[guard.lenReg] == span.rawLen) || (guard.lenReg < 0 && span.hasMin && guard.bound <= span.minLen)
	if inBounds {
		lanes := int64(1)
		if guard.slack > 0 {
			lanes = guard.slack
		}
		c.regions[dest.Num] = rvRegion{size: span.elem, writable: span.writable, rawLen: span.rawLen, idxReg: idxReg, idxGen: idxGen, lanes: lanes}
	}
}

// deriveFrameRegion records `add rD, base, t` as the address of one element
// of an owned array in the frame (docs/spec/94-assembler.md §9): base holds
// a frame address, t is an index guarded below a constant K (`li k, K`
// then `bgeu idx, k, trap`), scaled by 2^s — and every one of the K
// elements of 2^s bytes lies inside the declared frame, the base aligned
// to the element. The element is writable: the storage is the function's.
func (pre rvSnapshot) deriveFrameRegion(c *rvChecker, dest, left, right Register) {
	base, offset := left, right
	addr, isFrame := pre.frameAddrs[base.Num]
	if !isFrame {
		base, offset = right, left
		addr, isFrame = pre.frameAddrs[base.Num]
	}
	if !isFrame {
		pre.deriveTableRegion(c, dest, left, right)
		return
	}
	if dest.Num == base.Num {
		return
	}
	guard, guarded := pre.idx[offset.Num]
	shift := 0
	if scale, isScaled := pre.scaled[offset.Num]; isScaled {
		guard, guarded, shift = scale.guard, true, scale.shift
	}
	if !guarded || guard.lenReg >= 0 || guard.bound <= 0 {
		return
	}
	size := int64(1) << uint(shift)
	if addr%size != 0 || addr < -c.fn.Frame || addr+guard.bound*size > 0 {
		return
	}
	c.regions[dest.Num] = rvRegion{size: size, writable: true, rawLen: -1, idxReg: -2, frame: true}
}

// deriveTableRegion records `add rD, table, t` as one element of a
// constant data symbol (`la`): t is an index guarded below a constant K,
// scaled by 2^s, with every one of the K elements inside the table.
func (pre rvSnapshot) deriveTableRegion(c *rvChecker, dest, left, right Register) {
	base, offset := left, right
	table, isTable := pre.regions[base.Num]
	if !isTable || !table.table {
		base, offset = right, left
		table, isTable = pre.regions[base.Num]
	}
	if !isTable || !table.table || dest.Num == base.Num {
		return
	}
	guard, guarded := pre.idx[offset.Num]
	shift := 0
	if scale, isScaled := pre.scaled[offset.Num]; isScaled {
		guard, guarded, shift = scale.guard, true, scale.shift
	}
	if !guarded || guard.lenReg >= 0 || guard.bound <= 0 {
		return
	}
	size := int64(1) << uint(shift)
	if guard.bound*size > table.size {
		return
	}
	c.regions[dest.Num] = rvRegion{size: size, rawLen: -1, idxReg: -2}
}

// deriveSlack records `sub rD, len, k` (or `addi rD, len, -K`) as len - K
// when len is a normalized length register whose span is proven at least
// K long (`bltu len, k, trap` before it): the subtraction does not wrap,
// and a later `bltu rD, idx, trap` proves idx + K <= len — the bound of a
// K-element vector access at idx (docs/spec/94-assembler.md §9,
// Oak.RiscV.slack_guard).
func (pre rvSnapshot) deriveSlack(c *rvChecker, dest, left Register, k int64) {
	if dest.Class != ClassRV64X || left.Class != ClassRV64X || dest.Num == 0 || k <= 0 {
		return
	}
	raw, isLen := pre.lenNorm[left.Num]
	if !isLen {
		return
	}
	for _, span := range pre.spans {
		if span.rawLen == raw && span.hasMin && span.minLen >= k {
			c.slack[dest.Num] = rvSlackFact{lenReg: left.Num, k: k}
			return
		}
	}
}

// deriveRemaining records `sub rD, len, idx` as the remaining count when
// len is a normalized length register and idx is guarded below it: the
// AVL a strip-mining loop hands to vsetvli (docs/spec/94-assembler.md §9,
// Oak.RiscV.strip_access_in_bounds).
func (pre rvSnapshot) deriveRemaining(c *rvChecker, dest, left, right Register) {
	if dest.Class != ClassRV64X || left.Class != ClassRV64X || right.Class != ClassRV64X || dest.Num == 0 {
		return
	}
	if _, isLen := pre.lenNorm[left.Num]; !isLen {
		return
	}
	guard, guarded := pre.idx[right.Num]
	if !guarded || guard.lenReg != left.Num {
		return
	}
	c.rem[dest.Num] = rvRemFact{lenReg: left.Num, idxReg: right.Num, idxGen: pre.gen[right.Num]}
}

// vectorInstruction checks one vector instruction (docs/spec/94-assembler.md
// §9). vsetvli/vsetivli establish the configuration; every other vector
// instruction needs one in effect on its straight-line path. Loads and
// stores are proven through vectorAccess; register operations read their
// sources and write their destination.
func (c *rvChecker) vectorInstruction(base Instruction, shape string, line int) bool {
	c.usesVectorFile = true
	ops := base.Operands
	name := base.Mnemonic
	reg := func(i int) Register { return ops[i].(Register) }
	masked := rv64Masked(base)
	if masked {
		ops = ops[:len(ops)-1]
	}
	switch name {
	case "vsetvli", "vsetivli":
		cfg := &rvVectorConfig{sew: rv64VTypeSEW[ops[2].(Option).Name], lmul8: 8, avlImm: -1, line: line}
		lmulName := ops[3].(Option).Name
		lmul8, known := rv64LMULEighths[lmulName]
		if !known {
			c.errorf(line, "%s: LMUL %s is not one of mf8, mf4, mf2, m1, m2, m4, m8", name, lmulName)
			lmul8 = 8
		}
		cfg.lmul8 = lmul8
		// A fractional LMUL narrows the elements a register holds: the
		// ratio SEW/LMUL stays within ELEN = 64 (RVV 1.0 §3.4.2, vill
		// otherwise; Oak.RiscV.fractional_within_elen), so e64 needs at
		// least m1, e32 at least mf2, e16 at least mf4.
		if cfg.sew*8*8 > 64*lmul8 {
			c.errorf(line, "%s: e%d at %s puts SEW/LMUL past ELEN=64 (the configuration would be reserved); e%d needs LMUL at least %s", name, cfg.sew*8, lmulName, cfg.sew*8, rv64LMULName(cfg.sew*8*8/64))
		}
		if name == "vsetvli" {
			avl := reg(1)
			c.read(avl, line)
			if avl.Class == ClassRV64X {
				if fact, has := c.rem[avl.Num]; has {
					copied := fact
					cfg.rem = &copied
				} else if _, isLen := c.lenNorm[avl.Num]; isLen {
					cfg.rem = &rvRemFact{lenReg: avl.Num, idxReg: -1}
				}
			}
		} else {
			cfg.avlImm = ops[1].(Immediate).Value
		}
		// rd receives vl; the write drops any fact rd held (zero discards it).
		c.write(reg(0), line)
		c.vcfg = cfg
		return false
	}
	if c.vcfg == nil {
		c.errorf(line, "%s without a vector configuration in effect: vsetvli (or vsetivli) precedes every vector instruction on its straight-line path — labels and calls forget the configuration", name)
		return false
	}
	if masked {
		// The mask is v0, read as one register; the masked-off elements
		// are a subset of the vl elements every bound below already covers
		// (Oak.RiscV.masked_access_in_bounds).
		c.read(Register{Text: "v0", Class: ClassRV64V, Num: 0, Lane: -1}, line)
	}
	// Vector register operands are groups of EMUL registers (RVV 1.0
	// §3.4.2, §11.2): LMUL, twice LMUL for a widening destination or a
	// narrowing source, half for an extension's source; aligned to their
	// size, every register of the group read or written. A widening or
	// narrowing destination must not overlap a source (the ISA's overlap
	// rule, applied fail-closed), and the wide group stays within the file
	// and its element width within 64 bits (Oak.RiscV.wide_group_within_file).
	groupSize := func(position int) int64 {
		if rv64GroupSingle(name, position) {
			return 1
		}
		emul8 := c.vcfg.lmul8
		switch rv64VectorEMUL(name, position) {
		case 2:
			emul8 *= 2
		case 0:
			emul8 /= 2
		}
		return rv64GroupOf(emul8)
	}
	if rv64VectorEMUL(name, 0) == 2 || rv64VectorEMUL(name, 1) == 2 {
		if c.vcfg.lmul8*2 > 64 {
			c.errorf(line, "%s: the wide group would be LMUL=%s, past the file's eight registers", name, rv64LMULName(c.vcfg.lmul8*2))
			return false
		}
		if rv64VectorEMUL(name, 0) == 2 && c.vcfg.sew*2 > 8 {
			c.errorf(line, "%s: widening past 64-bit elements (SEW is e%d)", name, c.vcfg.sew*8)
			return false
		}
	}
	if (name == "vzext.vf2" || name == "vsext.vf2") && c.vcfg.sew < 2 {
		c.errorf(line, "%s: the source elements would be narrower than 8 bits (SEW is e8)", name)
		return false
	}
	if (name == "vzext.vf2" || name == "vsext.vf2") && c.vcfg.lmul8 < 2 {
		c.errorf(line, "%s: the source group would be LMUL=%s/2, below mf8", name, rv64LMULName(c.vcfg.lmul8))
		return false
	}
	// The floating-point forms need single- or double-precision elements
	// (RVV 1.0 §13: Zve32f gives e32, Zve64d e64; e8 has no float format
	// and e16 needs Zvfh, which the lane does not assume).
	if rv64VectorFloat[name] && c.vcfg.sew < 4 {
		c.errorf(line, "%s: the floating-point forms need e32 or e64 elements (SEW is e%d)", name, c.vcfg.sew*8)
		return false
	}
	group := func(position int, write bool) {
		r, isReg := ops[position].(Register)
		if !isReg {
			return // an immediate (vnsrl.wi's shift)
		}
		if r.Class != ClassRV64V {
			if write {
				c.write(r, line)
			} else {
				c.read(r, line)
			}
			return
		}
		count := groupSize(position)
		if int64(r.Num)%count != 0 {
			c.errorf(line, "%s: %s is not aligned to the register group of LMUL=%s (Oak.RiscV.group_within_file)", name, r.Text, rv64LMULName(count*8))
			return
		}
		for k := int64(0); k < count; k++ {
			member := Register{Text: fmt.Sprintf("v%d", int64(r.Num)+k), Class: ClassRV64V, Num: int(int64(r.Num) + k), Lane: -1}
			if write {
				c.write(member, line)
			} else {
				c.read(member, line)
			}
		}
	}
	if rv64VectorEMUL(name, 0) == 2 || rv64VectorEMUL(name, 1) == 2 || rv64VectorEMUL(name, 1) == 0 {
		// Destination and source groups of different sizes must not overlap.
		d := reg(0)
		if d.Class == ClassRV64V {
			dLo, dHi := int64(d.Num), int64(d.Num)+groupSize(0)-1
			for i := 1; i < len(shape); i++ {
				src, isReg := ops[i].(Register)
				if !isReg || src.Class != ClassRV64V {
					continue
				}
				sLo, sHi := int64(src.Num), int64(src.Num)+groupSize(i)-1
				if dLo <= sHi && sLo <= dHi {
					c.errorf(line, "%s: the destination group %s overlaps the source group %s; widening and narrowing groups must be disjoint", name, d.Text, src.Text)
					return false
				}
			}
		}
	}
	if rv64VectorDisjoint[name] {
		d := reg(0)
		dLo, dHi := int64(d.Num), int64(d.Num)+groupSize(0)-1
		for i := 1; i < len(shape); i++ {
			src, isReg := ops[i].(Register)
			if !isReg || src.Class != ClassRV64V {
				continue
			}
			sLo, sHi := int64(src.Num), int64(src.Num)+groupSize(i)-1
			if dLo <= sHi && sLo <= dHi {
				c.errorf(line, "%s: the destination group %s overlaps the source group %s; a gather's or a slide's destination is disjoint from its sources (RVV 1.0 §16.3, §16.4)", name, d.Text, src.Text)
				return false
			}
		}
	}
	if width, isLoad := rv64VectorLoads[name]; isLoad {
		c.vectorAccess(ops[1].(Memory), width, false, line)
		group(0, true)
		return false
	}
	if width, isStore := rv64VectorStores[name]; isStore {
		group(0, false)
		c.vectorAccess(ops[1].(Memory), width, true, line)
		return false
	}
	for i := 1; i < len(shape); i++ {
		group(i, false)
	}
	if name == "vfmacc.vv" {
		group(0, false) // the accumulator: vd = vs1 * vs2 + vd
	}
	group(0, true)
	return false
}

// vectorAccess checks a unit-stride vector load or store: the element
// width is the configured SEW, and the vl elements at the base lie within
// a span — through the span's base when the AVL is its normalized length
// (vl ≤ len) or an immediate within a proven minimum length, or through a
// guarded element address &v[idx] when the AVL is `len - idx` over the same
// index at the same write generation (idx + vl ≤ len,
// Oak.RiscV.strip_access_in_bounds). Stores need a writable span.
func (c *rvChecker) vectorAccess(mem Memory, width int64, store bool, line int) {
	cfg := c.vcfg
	base := mem.Base
	if base.Class != ClassRV64X {
		c.errorf(line, "vector memory through %s is not admitted", base.Text)
		return
	}
	c.read(base, line)
	if width != cfg.sew {
		c.errorf(line, "a %d-byte vector access under an e%d configuration: the element width and the SEW agree in this increment", width, cfg.sew*8)
		return
	}
	if span, isSpan := c.spans[base.Num]; isSpan {
		if width != span.elem {
			c.errorf(line, "%d-byte vector elements through %s, whose elements are %d bytes", width, base.Text, span.elem)
			return
		}
		if store && !span.writable {
			c.errorf(line, "vector store through %s into a read-only view", base.Text)
			return
		}
		if cfg.rem != nil && cfg.rem.idxReg == -1 {
			if raw, isLen := c.lenNorm[cfg.rem.lenReg]; isLen && raw == span.rawLen {
				return // vl ≤ AVL = len
			}
		}
		if cfg.avlImm >= 0 && span.hasMin && cfg.avlImm <= span.minLen {
			return // vl ≤ AVL = k ≤ the proven minimum length
		}
		c.errorf(line, "vector access through the span base %s: the configuration's AVL is neither the span's normalized length (`vsetvli rd, len, …`) nor an immediate within a proven minimum length (`bltu len, K` then `vsetivli rd, k` with k ≤ K)", base.Text)
		return
	}
	if region, isRegion := c.regions[base.Num]; isRegion {
		if width != region.size {
			c.errorf(line, "%d-byte vector elements through %s, an address of %d-byte elements", width, base.Text, region.size)
			return
		}
		if store && !region.writable {
			c.errorf(line, "vector store through %s into a read-only view", base.Text)
			return
		}
		if cfg.rem != nil && cfg.rem.idxReg >= 0 && region.idxReg == cfg.rem.idxReg && region.idxGen == cfg.rem.idxGen {
			if raw, isLen := c.lenNorm[cfg.rem.lenReg]; isLen && raw == region.rawLen {
				return // idx + vl ≤ idx + (len - idx) = len
			}
		}
		if cfg.avlImm > 0 && cfg.avlImm <= region.lanes {
			return // idx + vl ≤ idx + K ≤ len (Oak.RiscV.slack_access_in_bounds)
		}
		c.errorf(line, "vector access through the element address %s: the configuration's AVL must be `sub avl, len, idx` over the same guarded index the address was formed from, with neither rewritten in between (Oak.RiscV.strip_access_in_bounds), or an immediate within the K elements a slack guard proved (`bltu len, k; sub t, len, k; bltu t, idx` — Oak.RiscV.slack_access_in_bounds)", base.Text)
		return
	}
	if addr, isFrame := c.frameAddrs[base.Num]; isFrame {
		// A fixed vector in the frame (a vector local's sixteen-byte slot,
		// an owned array's element): an immediate AVL of K elements of the
		// configured width at an entry-relative frame address, inside the
		// declared frame (Oak.RiscV.frame_vector_in_bounds).
		if cfg.avlImm <= 0 {
			c.errorf(line, "vector access through the frame address %s needs an immediate AVL (vsetivli): the frame holds fixed vectors", base.Text)
			return
		}
		bytes := cfg.avlImm * width
		if addr < -c.fn.Frame || addr+bytes > 0 {
			c.errorf(line, "vector access at entry-relative %d..%d through %s is outside the declared frame [-%d, 0)", addr, addr+bytes, base.Text, c.fn.Frame)
			return
		}
		if addr%width != 0 {
			c.errorf(line, "vector access at %d through %s is not aligned to its %d-byte elements", addr, base.Text, width)
		}
		return
	}
	c.errorf(line, "vector memory through %s: only a bound span base, a guarded element address, or a frame address is admitted", base.Text)
}

// spanAccess checks a load or store through a register other than sp: an
// element region (the access inside it), or a span base at a constant
// offset below its proven minimum length. Stores need a writable span.
func (c *rvChecker) spanAccess(mem Memory, width int64, store bool, line int) {
	base := mem.Base
	if base.Class != ClassRV64X {
		c.errorf(line, "memory through %s is not admitted", base.Text)
		return
	}
	if region, isRegion := c.regions[base.Num]; isRegion {
		if region.global && (mem.Offset != 0 || width != region.size) {
			c.errorf(line, "%d-byte access at offset %d through %s: a global is one cell of %d bytes at its address", width, mem.Offset, base.Text, region.size)
			return
		}
		if mem.Offset < 0 || mem.Offset+width > region.size {
			c.errorf(line, "access at %d..%d through %s is outside its %d-byte element", mem.Offset, mem.Offset+width, base.Text, region.size)
			return
		}
		if store && !region.writable {
			c.errorf(line, "store through %s into a read-only view", base.Text)
		}
		return
	}
	if span, isSpan := c.spans[base.Num]; isSpan {
		if !span.hasMin {
			c.errorf(line, "access through the span base %s without a length guard: compare its normalized length (slli/srli 32) against a constant with bltu first, or address an element through a guarded index", base.Text)
			return
		}
		if width != span.elem || mem.Offset < 0 || mem.Offset%span.elem != 0 {
			c.errorf(line, "access of %d bytes at offset %d through %s: elements are %d bytes at multiples of %d", width, mem.Offset, base.Text, span.elem, span.elem)
			return
		}
		if mem.Offset+width > span.minLen*span.elem {
			c.errorf(line, "offset %d through %s reaches past the %d elements the guard proved", mem.Offset, base.Text, span.minLen)
			return
		}
		if store && !span.writable {
			c.errorf(line, "store through %s into a read-only view", base.Text)
		}
		return
	}
	if _, isFrame := c.frameAddrs[base.Num]; isFrame {
		c.errorf(line, "memory through the frame address %s without a guarded element: `li k, K; bgeu idx, k, <trap>; slli idx, idx, s; add e, %s, idx` forms an element of the owned array (K elements of 2^s bytes inside the frame)", base.Text, base.Text)
		return
	}
	c.errorf(line, "memory through %s: only the sp frame, a bound span base under a length guard, or a guarded element address is admitted", base.Text)
}
