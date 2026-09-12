package asm

import (
	"fmt"

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

	bound     map[int]bool // contract registers holding parameters
	clobbered map[int]bool // declared clobbers
	written   map[int]bool // registers written on this path
	freed     map[int]bool // caller-saved registers released by a call
	saved     map[int]*savedState

	disp        int64
	labelDisp   map[string]int64
	labels      map[string]bool
	unreachable bool
}

func checkRV64(fn *Function, decl *ast.FunctionStatement, symbols map[string]bool) []string {
	c := &rvChecker{fn: fn, symbols: symbols, bound: map[int]bool{}, clobbered: map[int]bool{}, written: map[int]bool{}, freed: map[int]bool{}, saved: map[int]*savedState{}, labelDisp: map[string]int64{}, labels: map[string]bool{}}
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
	c.walk()
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
	expect := map[string]int{}
	expectLen := map[string]int{}
	for _, param := range sig.Parameters {
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
			c.errorf(c.fn.Line, "parameter %s has type %s, which the rv64 contract does not carry in this increment", param.Name.Value, typeText(param.Type))
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
		if typeText(sig.ReturnType) == "never" {
			c.never = true
		} else if class, ok := contractClass(sig.ReturnType); !ok || class == ClassV {
			c.errorf(c.fn.Line, "result type %s is not carried by the rv64 contract in this increment", typeText(sig.ReturnType))
		} else {
			c.hasResult = true
		}
	}
	seen := map[string]bool{}
	for _, b := range c.fn.Bindings {
		want, declared := expect[b.Param]
		if !declared {
			c.errorf(b.Line, "bind names %s, which is not a parameter", b.Param)
			continue
		}
		if seen[b.Param] {
			c.errorf(b.Line, "parameter %s is bound twice", b.Param)
			continue
		}
		seen[b.Param] = true
		if b.Register.Class != ClassRV64X || b.Register.Num != want {
			c.errorf(b.Line, "parameter %s must be bound to %s (its LP64 contract register), not %s", b.Param, rv64RegisterName(want), b.Register.Text)
			continue
		}
		if lenReg, isSpan := expectLen[b.Param]; isSpan {
			if b.Length == nil || b.Length.Class != ClassRV64X || b.Length.Num != lenReg {
				c.errorf(b.Line, "span parameter %s binds its {base, len} pair as `bind %s, %s = %s`", b.Param, rv64RegisterName(want), rv64RegisterName(lenReg), b.Param)
				continue
			}
			c.bound[lenReg] = true
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
	for _, reg := range c.fn.Clobbers {
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
	if reg.Class != ClassRV64X {
		return
	}
	num := reg.Num
	switch {
	case num == 0:
		return // a write to zero is discarded
	case num == 10 && c.hasResult, c.bound[num], c.clobbered[num], c.freed[num]:
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

func (c *rvChecker) enterLabel(label Label) {
	c.unreachable = false
	if known, has := c.labelDisp[label.Name]; has {
		if known != c.disp {
			c.errorf(label.Line, "sp displacement %d at label %s disagrees with %d on another path", c.disp, label.Name, known)
		}
		c.disp = known
		return
	}
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
	for num := 5; num <= 31; num++ {
		if num >= 5 && num <= 7 || num >= 10 && num <= 17 || num >= 28 {
			delete(c.written, num)
			delete(c.bound, num)
			c.freed[num] = true
		}
	}
	c.written[10] = true // the callee's result
}

// instruction checks one instruction; true when it ends the path.
func (c *rvChecker) instruction(instr Instruction) bool {
	line := instr.Line
	base := rv64Base(instr)
	name := base.Mnemonic
	ops := base.Operands
	reg := func(i int) Register { return ops[i].(Register) }
	if rv64Branches[name] {
		c.read(reg(0), line)
		c.read(reg(1), line)
		c.branchTo(ops[2].(Symbol).Name, line)
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
	case "li":
		imm := ops[1].(Immediate).Value
		if imm < -(1<<31) || imm >= 1<<31 {
			c.errorf(line, "li admits 32-bit immediates in this increment (%d)", imm)
		}
		c.write(reg(0), line)
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
	case "ecall", "ebreak", "fence":
		c.errorf(line, "%s is outside the rv64 subset of this increment", name)
		return false
	}
	if width, isLoad := rv64Loads[name]; isLoad {
		mem := ops[1].(Memory)
		addr, ok := c.frameAddress(mem, int64(width), line)
		dest := reg(0)
		if ok && dest.Class == ClassRV64X && rv64Preserved(dest.Num) {
			state := c.saved[dest.Num]
			if state.saved && width == 8 && state.slot == addr {
				// The restore: the caller's value is back.
				state.restored = true
				state.written = false
				delete(c.written, dest.Num)
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
		c.write(reg(0), line)
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
		c.write(reg(0), line)
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
	c.unreachable = true
	return true
}
