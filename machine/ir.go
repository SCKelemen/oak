// Package machine is the native lane's machine-level intermediate
// representation (docs/notes/optimizer-search-2026-09.md §10.1, Phase B):
// a lowered body as blocks of instructions over registers, with each
// instruction's definitions and uses made explicit, a control-flow graph,
// global liveness, and def-use webs that serve as virtual registers for a
// global register allocator.
//
// The package lifts the assembly the lowering emitted (asm.Function) and
// lowers the reallocated body back to it. It is untrusted: every body it
// produces passes the seam checker and the semantic verifier before use,
// and an instruction shape it does not know refuses the lift so the plain
// lowering stands (docs/spec/90-backend.md §16 rule 3).
package machine

import (
	"fmt"
	"strconv"

	"github.com/SCKelemen/oak/asm"
)

// Class is a register file: the general registers x0–x30 or the vector
// registers v0–v31.
type Class int

const (
	GPR Class = iota
	VEC
)

func (c Class) String() string {
	switch c {
	case VEC:
		return "v"
	case FPR:
		return "f"
	case SLOT:
		return "slot"
	}
	return "x"
}

// Reg is a physical register: its file and number. The zero register
// (x31) and sp are not registers here — they are never allocated.
type Reg struct {
	Class Class
	Num   int
}

func (r Reg) String() string { return r.Class.String() + strconv.Itoa(r.Num) }

// part locates a register inside an operand: the register itself or a
// memory operand's base (partReg), a memory operand's index (partIndex),
// or the k-th register of a register list (partList+k).
const (
	partReg   = 0
	partIndex = 1
	partList  = 2
)

// Access is one register read or write of an instruction: where it sits
// (operand and part; Implicit for the contract registers a call or a
// return touches without naming them), which register, and the width of
// the view in bits.
type Access struct {
	Op       int
	Part     int
	Implicit bool
	Reg      Reg
	Bits     int
	// Lane marks a lane view (v0.s[1]): a read of one element, or an
	// insertion that also reads the register.
	Lane bool
}

// Instr is one instruction with its accesses.
type Instr struct {
	Index int // position in the function's linear order
	Asm   asm.Instruction
	Defs  []Access
	Uses  []Access
	// Call marks bl/blr; Ret a return; Branch a branch (conditional or
	// not); Trap brk.
	Call, Ret, Branch, Trap bool
	// Copy marks a register-to-register copy of CopyBits bits between
	// Uses[0] and Defs[0]: mov xD, xS; fmov dD, dS; orr vD.16b, vS.16b,
	// vS.16b.
	Copy     bool
	CopyBits int
	Block    *Block
}

// Block is a maximal straight-line sequence: it begins at a label or after
// a terminator and ends at a terminator or before a label.
type Block struct {
	Index int
	Label string // "" for the entry block or a fall-through block without one
	// Lead holds the items before the first instruction (the label, an
	// alignment directive), as they were.
	Lead   []asm.Item
	Instrs []*Instr
	Succs  []*Block
	Preds  []*Block
}

// Function is a lifted body.
type Function struct {
	Asm    *asm.Function
	Blocks []*Block
	Instrs []*Instr // every instruction in linear order
	labels map[string]*Block
	t      *target
}

// shape is an instruction's register semantics: the operands it writes,
// whether it also reads its first operand (an accumulating form), and
// whether a register list in its first operand is written.
type shape struct {
	defs    []int
	accum   bool
	listDef bool
}

var def0 = shape{defs: []int{0}}
var def01 = shape{defs: []int{0, 1}}
var accum0 = shape{defs: []int{0}, accum: true}
var noDef = shape{}

// shapes are the AArch64 instructions the lift knows. Anything else
// refuses the lift.
var shapes = map[string]shape{}

func init() {
	for _, m := range []string{
		"mov", "movz", "movn", "mvn", "neg", "negs", "add", "adds", "sub", "subs", "mul", "madd", "msub", "mneg",
		"smull", "umull", "smulh", "umulh", "umaddl", "smaddl", "umsubl", "smsubl", "udiv", "sdiv",
		"and", "ands", "orr", "orn", "eor", "eon", "bic", "bics", "lsl", "lsr", "asr", "ror", "lslv", "lsrv", "asrv", "rorv",
		"clz", "cls", "rbit", "cnt", "rev", "rev16", "rev32", "rev64", "sxtb", "sxth", "sxtw", "uxtb", "uxth",
		"ubfx", "sbfx", "ubfiz", "sbfiz", "extr", "csel", "cset", "csetm", "csinc", "csinv", "csneg", "cneg", "cinc", "cinv",
		"adr", "adrp", "adrl",
		"ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "ldrsw", "ldur", "ldurb", "ldurh", "ldar", "ldarb", "ldarh", "ldaxr", "ldxr", "ldaxrb", "ldxrb", "ldaxrh", "ldxrh",
		"stxr", "stlxr", "stxrb", "stlxrb", "stxrh", "stlxrh", // the status register is written
		"fmov", "fadd", "fsub", "fmul", "fdiv", "fneg", "fabs", "fsqrt", "fmax", "fmin", "fmaxnm", "fminnm", "fmadd", "fmsub", "fnmadd", "fnmsub", "fnmul",
		"fcvt", "fcvtzs", "fcvtzu", "fcvtns", "fcvtnu", "fcvtms", "fcvtmu", "fcvtps", "fcvtpu", "fcvtas", "fcvtau", "fcvtl", "fcvtn", "fcvtxn",
		"frintz", "frintm", "frintp", "frinta", "frintn", "frintx", "frinti", "scvtf", "ucvtf", "fcsel",
		"dup", "movi", "mvni", "ext", "tbl", "cmeq", "cmhi", "cmhs", "cmgt", "cmge", "cmle", "cmlt", "cmtst", "fcmeq", "fcmgt", "fcmge", "fcmlt", "fcmle",
		"addv", "uaddlv", "saddlv", "umaxv", "uminv", "smaxv", "sminv", "fmaxv", "fminv", "fmaxnmv", "fminnmv", "umov", "smov",
		"shl", "sshr", "ushr", "sshl", "ushl", "sqshl", "uqshl", "shrn", "rshrn", "sshll", "ushll", "uxtl", "sxtl", "xtn", "uqxtn", "sqxtn", "sqxtun",
		"uzp1", "uzp2", "zip1", "zip2", "trn1", "trn2", "addp", "faddp", "fmaxp", "fminp", "umax", "umin", "smax", "smin", "umaxp", "uminp", "smaxp", "sminp",
		"uaddl", "uaddw", "usubl", "usubw", "saddl", "saddw", "ssubl", "ssubw", "abs", "sqadd", "uqadd", "sqsub", "uqsub", "urhadd", "uhadd", "shadd", "srhadd", "not", "mvn",
		"pmul", "pmull", "pmull2", "uabd", "sabd", "fabd", "frecpe", "frsqrte", "fcvtzs", "fcvtzu", "ucvtf", "scvtf", "rev64", "rev32", "rev16", "eor3", "rax1", "xar", "bcax",
	} {
		shapes[m] = def0
	}
	for _, m := range []string{"movk", "fmla", "fmls", "mla", "mls", "bsl", "bit", "bif", "ins", "umlal", "smlal", "umlal2", "smlal2", "umlsl", "smlsl", "sadalp", "uadalp", "bfi", "bfxil", "sli", "sri", "sha256h", "sha256h2", "sha256su0", "sha256su1", "sha1c", "sha1p", "sha1m", "sha1su0", "sha1su1", "aese", "aesd", "aesmc", "aesimc", "crc32b", "crc32h", "crc32w", "crc32x", "crc32cb", "crc32ch", "crc32cw", "crc32cx"} {
		shapes[m] = accum0
	}
	// crc32* write op0 from op1 and op2 without reading op0; the accumulating
	// reading is harmless (conservative).
	for _, m := range []string{"ldp", "ldpsw", "ldaxp", "ldxp"} {
		shapes[m] = def01
	}
	for _, m := range []string{"str", "strb", "strh", "stp", "stur", "sturb", "sturh", "stlr", "stlrb", "stlrh", "st1", "st2", "st3", "st4",
		"cmp", "cmn", "tst", "fcmp", "fcmpe", "ccmp", "ccmn",
		"b", "b.", "cbz", "cbnz", "tbz", "tbnz", "ret", "brk", "dmb", "dsb", "isb", "nop", "hint", "yield", "sev", "sevl", "wfe", "wfi", "prfm", "bl", "blr"} {
		shapes[m] = noDef
	}
	for _, m := range []string{"ld1", "ld2", "ld3", "ld4", "ld1r", "ld2r", "ld3r", "ld4r"} {
		shapes[m] = shape{defs: []int{0}, listDef: true}
	}
}

// Lift reads an emitted AArch64 body into the representation. An
// instruction, operand, or control shape the lift does not know is an
// error: the body keeps its lowering as emitted.
func Lift(fn *asm.Function) (*Function, error) {
	if fn == nil {
		return nil, fmt.Errorf("machine: no function")
	}
	t, err := targetFor(fn.Arch)
	if err != nil {
		return nil, err
	}
	out := &Function{Asm: fn, labels: map[string]*Block{}, t: t}
	if err := out.buildBlocks(); err != nil {
		return nil, err
	}
	for _, ins := range out.Instrs {
		if err := accesses(t, ins); err != nil {
			return nil, fmt.Errorf("machine: line %d: %v", ins.Asm.Line, err)
		}
	}
	if err := out.connect(); err != nil {
		return nil, err
	}
	return out, nil
}

// terminator reports an instruction that ends a block: a branch, a
// return, a trap, or a jump the lift refuses.
func (t *target) terminator(ins asm.Instruction) bool {
	_, ret, trap, branch, err := t.kind(ins)
	return ret || trap || branch || err != nil
}

// branchTarget is the label a branch names, "" for none.
func branchTarget(ins asm.Instruction) string {
	if len(ins.Operands) == 0 {
		return ""
	}
	if sym, ok := ins.Operands[len(ins.Operands)-1].(asm.Symbol); ok && !sym.Lo12 {
		return sym.Name
	}
	return ""
}

// accesses fills an instruction's defs and uses from its shape.
func accesses(t *target, ins *Instr) error {
	a := ins.Asm
	sh, known := t.shapes[a.Mnemonic]
	if !known {
		return fmt.Errorf("unknown instruction %s", a.Mnemonic)
	}
	call, ret, trap, branch, err := t.kind(a)
	if err != nil {
		return err
	}
	ins.Call, ins.Ret, ins.Trap, ins.Branch = call, ret, trap, branch
	isDef := map[int]bool{}
	for _, d := range sh.defs {
		isDef[d] = true
	}
	for i, op := range a.Operands {
		switch o := op.(type) {
		case asm.Register:
			r, bits, lane, ok, err := t.regOf(o)
			if err != nil {
				return err
			}
			if !ok {
				continue // sp, the zero register
			}
			acc := Access{Op: i, Part: partReg, Reg: r, Bits: bits, Lane: lane}
			if isDef[i] {
				if lane {
					// An element insertion writes part of the register: a
					// read and a write.
					ins.Uses = append(ins.Uses, acc)
				}
				ins.Defs = append(ins.Defs, acc)
				if sh.accum && i == 0 {
					ins.Uses = append(ins.Uses, acc)
				}
			} else {
				ins.Uses = append(ins.Uses, acc)
			}
		case asm.Memory:
			if o.Mode != asm.MemOffset {
				return fmt.Errorf("pre- or post-indexed memory operand")
			}
			if o.MulVL {
				return fmt.Errorf("scalable memory operand")
			}
			if r, bits, _, ok, err := t.regOf(o.Base); err != nil {
				return err
			} else if ok {
				ins.Uses = append(ins.Uses, Access{Op: i, Part: partReg, Reg: r, Bits: bits})
			}
			if o.Index != nil {
				if r, bits, _, ok, err := t.regOf(*o.Index); err != nil {
					return err
				} else if ok {
					ins.Uses = append(ins.Uses, Access{Op: i, Part: partIndex, Reg: r, Bits: bits})
				}
			}
		case asm.RegisterList:
			for k, reg := range o.Regs {
				r, bits, lane, ok, err := t.regOf(reg)
				if err != nil {
					return err
				}
				if !ok {
					return fmt.Errorf("register list of %s", reg.Text)
				}
				acc := Access{Op: i, Part: partList + k, Reg: r, Bits: bits, Lane: lane}
				if isDef[i] && sh.listDef {
					ins.Defs = append(ins.Defs, acc)
				} else {
					ins.Uses = append(ins.Uses, acc)
				}
			}
		case asm.Extended:
			if r, bits, lane, ok, err := t.regOf(o.Reg); err != nil {
				return err
			} else if ok {
				ins.Uses = append(ins.Uses, Access{Op: i, Part: partReg, Reg: r, Bits: bits, Lane: lane})
			}
		case asm.Shifted:
			if r, bits, lane, ok, err := t.regOf(o.Reg); err != nil {
				return err
			} else if ok {
				ins.Uses = append(ins.Uses, Access{Op: i, Part: partReg, Reg: r, Bits: bits, Lane: lane})
			}
		case asm.Immediate, asm.FloatImmediate, asm.Symbol, asm.Condition, asm.Option:
		case asm.SysReg, asm.TileSlice:
			return fmt.Errorf("operand %s", op.(interface{ operandKind() string }).operandKind())
		default:
			if kinded, ok := op.(interface{ operandKind() string }); ok {
				return fmt.Errorf("operand of kind %q", kinded.operandKind())
			}
			return fmt.Errorf("operand of an unknown kind (%T)", op)
		}
	}
	if ins.Call {
		// The procedure-call contract: the argument registers read, the
		// caller-saved registers written.
		ins.Uses = append(ins.Uses, t.callUses...)
		ins.Defs = append(ins.Defs, t.callDefs...)
	}
	if ins.Ret {
		ins.Uses = append(ins.Uses, t.retUses...)
	}
	if bits, ok := t.copyOf(a); ok && len(ins.Defs) == 1 && len(ins.Uses) >= 1 && ins.Defs[0].Reg.Class == ins.Uses[0].Reg.Class {
		ins.Copy, ins.CopyBits = true, bits
	}
	return nil
}

// regOf maps an assembly register to a Reg with the width of its view; ok
// is false for sp and the zero register, which are never allocated.
func regOf(r asm.Register) (reg Reg, bits int, lane bool, ok bool, err error) {
	switch r.Class {
	case asm.ClassSP:
		return Reg{}, 0, false, false, nil
	case asm.ClassX, asm.ClassW:
		if r.ZeroRegister() {
			return Reg{}, 0, false, false, nil
		}
		if r.Num < 0 || r.Num > 30 {
			return Reg{}, 0, false, false, fmt.Errorf("register %s", r.Text)
		}
		return Reg{GPR, r.Num}, viewBits(r), false, true, nil
	case asm.ClassV:
		if r.Num < 0 || r.Num > 31 {
			return Reg{}, 0, false, false, fmt.Errorf("register %s", r.Text)
		}
		return Reg{VEC, r.Num}, viewBits(r), r.Lane >= 0, true, nil
	}
	return Reg{}, 0, false, false, fmt.Errorf("register %s of a class the lift does not allocate", r.Text)
}

// viewBits is the width of a register view in bits: w 32, x 64, the
// vector scalar letters b/h/s/d/q 8–128, the arrangements 64 or 128, a
// whole vN 128, and a lane view the whole register (its element is part
// of it).
func viewBits(r asm.Register) int {
	switch r.Class {
	case asm.ClassW:
		return 32
	case asm.ClassX:
		return 64
	}
	if r.Lane >= 0 {
		return 128
	}
	switch r.Vec {
	case "b":
		return 8
	case "h":
		return 16
	case "s":
		return 32
	case "d", "8b", "4h", "2s", "1d":
		return 64
	}
	return 128
}

// spell rewrites an assembly register operand to a physical register,
// keeping its view.
func spell(r asm.Register, to Reg) asm.Register {
	out := r
	out.Num = to.Num
	switch r.Class {
	case asm.ClassX:
		out.Text = "x" + strconv.Itoa(to.Num)
	case asm.ClassW:
		out.Text = "w" + strconv.Itoa(to.Num)
	case asm.ClassV:
		n := strconv.Itoa(to.Num)
		switch {
		case r.Lane >= 0:
			out.Text = "v" + n + "." + r.Vec + "[" + strconv.Itoa(r.Lane) + "]"
		case r.Vec == "":
			out.Text = "v" + n
		case len(r.Vec) == 1:
			out.Text = r.Vec + n
		default:
			out.Text = "v" + n + "." + r.Vec
		}
	}
	return out
}

// regAt reads the register an access names inside its instruction.
func regAt(a asm.Instruction, acc Access) asm.Register {
	switch o := a.Operands[acc.Op].(type) {
	case asm.Register:
		return o
	case asm.Memory:
		if acc.Part == partIndex {
			return *o.Index
		}
		return o.Base
	case asm.RegisterList:
		return o.Regs[acc.Part-partList]
	case asm.Extended:
		return o.Reg
	case asm.Shifted:
		return o.Reg
	}
	return asm.Register{}
}

// setRegAt rewrites the register an access names.
func (t *target) setRegAt(a *asm.Instruction, acc Access, to Reg) {
	switch o := a.Operands[acc.Op].(type) {
	case asm.Register:
		a.Operands[acc.Op] = t.spell(o, to)
	case asm.Memory:
		if acc.Part == partIndex {
			idx := t.spell(*o.Index, to)
			o.Index = &idx
		} else {
			o.Base = t.spell(o.Base, to)
		}
		a.Operands[acc.Op] = o
	case asm.RegisterList:
		regs := append([]asm.Register(nil), o.Regs...)
		regs[acc.Part-partList] = t.spell(regs[acc.Part-partList], to)
		a.Operands[acc.Op] = asm.RegisterList{Regs: regs}
	case asm.Extended:
		o.Reg = t.spell(o.Reg, to)
		a.Operands[acc.Op] = o
	case asm.Shifted:
		o.Reg = t.spell(o.Reg, to)
		a.Operands[acc.Op] = o
	}
}

// Items lowers the function back to assembly items, in block order.
func (f *Function) Items() []asm.Item {
	var out []asm.Item
	for _, b := range f.Blocks {
		out = append(out, b.Lead...)
		for _, ins := range b.Instrs {
			out = append(out, ins.Asm)
		}
	}
	return out
}
