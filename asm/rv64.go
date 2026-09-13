package asm

import (
	"fmt"
	"strconv"
	"strings"
)

// The RISC-V lane (docs/spec/94-assembler.md §9): RV64IM units — the base
// integer set with the multiply extension, control transfer, and loads
// and stores — under the LP64 psABI. Units name the architecture in their
// file (`name.rv64.oakasm`) or with an `arch rv64` directive. The table is
// generated from riscv-opcodes (asm/rv64_encodings_gen.go); the
// pseudo-instructions below are the assembler's, spelled as their base
// encodings. The seam checker, the verifier's term language, the encoder,
// and the ELF writer follow the AArch64 lane's shape with the differences
// the ISA makes: no flags (a branch compares two registers), a link
// register `ra` instead of `x30`, and `sp` as x2.

const (
	ArchArm64 = "arm64"
	ArchRV64  = "rv64"
)

// rv64Encoding is one base instruction: the fixed bits and the argument
// fields by name (rd, rs1, rs2, imm12, imm20, jimm20, bimm12hi/lo,
// imm12hi/lo, shamtd, shamtw).
type rv64Encoding struct {
	Mnemonic string
	Mask     uint32
	Value    uint32
	Args     []rv64Arg
	Source   string
}

type rv64Arg struct {
	Name   string
	Hi, Lo int
}

// rv64Table indexes the generated encodings by mnemonic.
var rv64Table = func() map[string]*rv64Encoding {
	table := make(map[string]*rv64Encoding, len(rv64Encodings))
	for i := range rv64Encodings {
		table[rv64Encodings[i].Mnemonic] = &rv64Encodings[i]
	}
	return table
}()

// rv64Pseudo are the assembler's spellings: each is one base instruction
// (li and call may be two words).
var rv64Pseudo = map[string]bool{"mv": true, "li": true, "not": true, "neg": true, "negw": true, "sext.w": true, "j": true, "jr": true, "ret": true, "nop": true, "beqz": true, "bnez": true, "bgez": true, "bltz": true, "blez": true, "bgtz": true, "call": true}

// rv64Branches are the conditional branches: they compare two registers,
// so the checker's flags rule becomes the comparison-branch rule.
var rv64Branches = map[string]bool{"beq": true, "bne": true, "blt": true, "bge": true, "bltu": true, "bgeu": true}

// rv64Loads and rv64Stores map mnemonics to access widths in bytes; the
// unsigned loads zero-extend, the signed ones sign-extend.
var rv64Loads = map[string]int{"lb": 1, "lh": 2, "lw": 4, "ld": 8, "lbu": 1, "lhu": 2, "lwu": 4}
var rv64Stores = map[string]int{"sb": 1, "sh": 2, "sw": 4, "sd": 8}

// The F and D extensions (docs/spec/94-assembler.md §9): loads and stores
// of the floating-point file, the arithmetic, fused multiply-adds,
// comparisons (writing an integer register), conversions, and moves
// between the files. The verifier's term language does not reach them;
// a unit using them is checked and trusted.
var rv64FloatLoads = map[string]int{"flw": 4, "fld": 8}
var rv64FloatStores = map[string]int{"fsw": 4, "fsd": 8}

// rv64FloatShapes maps each F/D mnemonic to its operand classes: f for a
// floating-point register, x for an integer register, r for an optional
// rounding mode.
var rv64FloatShapes = map[string]string{
	"fadd.s": "fffr", "fsub.s": "fffr", "fmul.s": "fffr", "fdiv.s": "fffr", "fsqrt.s": "ffr",
	"fadd.d": "fffr", "fsub.d": "fffr", "fmul.d": "fffr", "fdiv.d": "fffr", "fsqrt.d": "ffr",
	"fmin.s": "fff", "fmax.s": "fff", "fmin.d": "fff", "fmax.d": "fff",
	"fsgnj.s": "fff", "fsgnjn.s": "fff", "fsgnjx.s": "fff", "fsgnj.d": "fff", "fsgnjn.d": "fff", "fsgnjx.d": "fff",
	"fmadd.s": "ffffr", "fmsub.s": "ffffr", "fnmadd.s": "ffffr", "fnmsub.s": "ffffr",
	"fmadd.d": "ffffr", "fmsub.d": "ffffr", "fnmadd.d": "ffffr", "fnmsub.d": "ffffr",
	"feq.s": "xff", "flt.s": "xff", "fle.s": "xff", "feq.d": "xff", "flt.d": "xff", "fle.d": "xff",
	"fclass.s": "xf", "fclass.d": "xf",
	"fmv.x.w": "xf", "fmv.w.x": "fx", "fmv.x.d": "xf", "fmv.d.x": "fx",
	"fcvt.w.s": "xfr", "fcvt.wu.s": "xfr", "fcvt.l.s": "xfr", "fcvt.lu.s": "xfr",
	"fcvt.w.d": "xfr", "fcvt.wu.d": "xfr", "fcvt.l.d": "xfr", "fcvt.lu.d": "xfr",
	"fcvt.s.w": "fxr", "fcvt.s.wu": "fxr", "fcvt.s.l": "fxr", "fcvt.s.lu": "fxr",
	"fcvt.d.w": "fxr", "fcvt.d.wu": "fxr", "fcvt.d.l": "fxr", "fcvt.d.lu": "fxr",
	"fcvt.s.d": "ffr", "fcvt.d.s": "ffr",
}

// The vector extension (docs/spec/94-assembler.md §9, RVV 1.0): the
// landed subset is configuration (vsetvli/vsetivli with an explicit
// vtype), unit-stride loads and stores of 8- and 32-bit elements, the
// lane-wise integer operations, the mask producers and consumers, and the
// sum reduction. rv64VectorShapes gives each mnemonic's operand classes:
// v a vector register, x an integer register, m a memory operand `(base)`,
// i an immediate, o the four vtype options (e*, m*, ta|tu, ma|mu).
var rv64VectorShapes = map[string]string{
	"vsetvli": "xxoooo", "vsetivli": "xioooo",
	"vle8.v": "vm", "vle32.v": "vm", "vse8.v": "vm", "vse32.v": "vm",
	"vadd.vv": "vvv", "vsub.vv": "vvv", "vand.vv": "vvv", "vor.vv": "vvv", "vxor.vv": "vvv", "vminu.vv": "vvv", "vmaxu.vv": "vvv",
	"vmv.v.x": "vx", "vmv.x.s": "xv", "vredsum.vs": "vvv",
	"vmseq.vv": "vvv", "vmsne.vx": "vvx", "vmerge.vvm": "vvvv", "vcpop.m": "xv",
}

// rv64VectorLoads and rv64VectorStores map the unit-stride memory
// instructions to their element width in bytes (the EEW).
var rv64VectorLoads = map[string]int64{"vle8.v": 1, "vle32.v": 4}
var rv64VectorStores = map[string]int64{"vse8.v": 1, "vse32.v": 4}

// rv64VTypeSEW, rv64VTypeLMUL, and rv64VTypePolicy are the vtype fields
// (RVV 1.0 §3.4): vsew in bits 5:3 as the element width, vlmul in bits
// 2:0, vta bit 6, vma bit 7.
var rv64VTypeSEW = map[string]int64{"e8": 1, "e16": 2, "e32": 4, "e64": 8}
var rv64VTypeLMUL = map[string]int64{"m1": 0, "m2": 1, "m4": 2, "m8": 3, "mf8": 5, "mf4": 6, "mf2": 7}
var rv64VTypePolicy = map[string]bool{"ta": true, "tu": true, "ma": true, "mu": true}

// rv64VType encodes the vtype immediate of an explicit `e*, m*, ta|tu,
// ma|mu` option list (rv64CheckVectorShape admits exactly that order).
func rv64VType(options []Operand) int64 {
	sew := rv64VTypeSEW[options[0].(Option).Name]
	vsew := map[int64]int64{1: 0, 2: 1, 4: 2, 8: 3}[sew]
	vtype := rv64VTypeLMUL[options[1].(Option).Name] | vsew<<3
	if options[2].(Option).Name == "ta" {
		vtype |= 1 << 6
	}
	if options[3].(Option).Name == "ma" {
		vtype |= 1 << 7
	}
	return vtype
}

// rv64RoundingModes are the rounding-mode operands the arithmetic and
// conversions take; absent, the encoder uses dyn (the fcsr's mode).
var rv64RoundingModes = map[string]int64{"rne": 0, "rtz": 1, "rdn": 2, "rup": 3, "rmm": 4, "dyn": 7}

// rv64FloatABINames maps the floating-point ABI names to numbers.
var rv64FloatABINames = map[string]int{
	"ft0": 0, "ft1": 1, "ft2": 2, "ft3": 3, "ft4": 4, "ft5": 5, "ft6": 6, "ft7": 7,
	"fs0": 8, "fs1": 9,
	"fa0": 10, "fa1": 11, "fa2": 12, "fa3": 13, "fa4": 14, "fa5": 15, "fa6": 16, "fa7": 17,
	"fs2": 18, "fs3": 19, "fs4": 20, "fs5": 21, "fs6": 22, "fs7": 23, "fs8": 24, "fs9": 25, "fs10": 26, "fs11": 27,
	"ft8": 28, "ft9": 29, "ft10": 30, "ft11": 31,
}

// rv64FloatRegisterName is the ABI spelling of a floating-point register.
func rv64FloatRegisterName(num int) string {
	for name, n := range rv64FloatABINames {
		if n == num {
			return name
		}
	}
	return fmt.Sprintf("f%d", num)
}

// rv64FloatCalleeSaved reports fs0–fs11 (f8, f9, f18–f27).
func rv64FloatCalleeSaved(num int) bool { return num == 8 || num == 9 || (num >= 18 && num <= 27) }

// rv64ABINames maps the ABI register names to numbers; x2 is sp, parsed
// as ClassSP so the frame machinery shared with the AArch64 lane applies.
var rv64ABINames = map[string]int{
	"zero": 0, "ra": 1, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9,
	"a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15, "a6": 16, "a7": 17,
	"s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27,
	"t3": 28, "t4": 29, "t5": 30, "t6": 31,
}

// rv64RegisterName is the ABI spelling of a register number.
func rv64RegisterName(num int) string {
	for name, n := range rv64ABINames {
		if n == num && name != "fp" && name != "zero" {
			return name
		}
	}
	if num == 0 {
		return "zero"
	}
	return fmt.Sprintf("x%d", num)
}

// rv64CalleeSaved reports s0–s11 (x8, x9, x18–x27): the caller's, under
// the same save/restore-from-the-same-slot obligation as x19–x30.
func rv64CalleeSaved(num int) bool { return num == 8 || num == 9 || (num >= 18 && num <= 27) }

// parseRV64Register reads x0–x31, the ABI names, and sp.
func parseRV64Register(text string) (Register, bool) {
	lower := strings.ToLower(text)
	if lower == "sp" || lower == "x2" {
		return Register{Text: "sp", Class: ClassSP, Num: -1, Lane: -1}, true
	}
	if num, known := rv64ABINames[lower]; known {
		return Register{Text: lower, Class: ClassRV64X, Num: num, Lane: -1}, true
	}
	if strings.HasPrefix(lower, "x") {
		num, err := strconv.Atoi(lower[1:])
		if err == nil && num >= 0 && num <= 31 {
			return Register{Text: lower, Class: ClassRV64X, Num: num, Lane: -1}, true
		}
	}
	if num, known := rv64FloatABINames[lower]; known {
		return Register{Text: lower, Class: ClassRV64F, Num: num, Lane: -1}, true
	}
	if strings.HasPrefix(lower, "f") {
		num, err := strconv.Atoi(lower[1:])
		if err == nil && num >= 0 && num <= 31 {
			return Register{Text: lower, Class: ClassRV64F, Num: num, Lane: -1}, true
		}
	}
	if strings.HasPrefix(lower, "v") {
		num, err := strconv.Atoi(lower[1:])
		if err == nil && num >= 0 && num <= 31 {
			return Register{Text: lower, Class: ClassRV64V, Num: num, Lane: -1}, true
		}
	}
	return Register{}, false
}

// rv64Number is the physical register number of an operand register (sp is x2).
func rv64Number(reg Register) int {
	if reg.Class == ClassSP {
		return 2
	}
	return reg.Num
}

// parseRV64Instruction parses one instruction line: `mnemonic op, op, ...`
// with registers, bare immediates, `imm(base)` memory operands, and label
// or symbol names. `call sym` stays one item (two words in the encoder:
// auipc ra + jalr ra under R_RISCV_CALL_PLT).
func parseRV64Instruction(fields []string, lineNo int) ([]Instruction, error) {
	mnemonic := strings.ToLower(fields[0])
	if _, base := rv64Table[mnemonic]; !base && !rv64Pseudo[mnemonic] {
		return nil, fmt.Errorf("unknown instruction %q (not in the RV64IM table)", mnemonic)
	}
	var operands []Operand
	for _, text := range fields[1:] {
		operand, err := parseRV64Operand(text, mnemonic)
		if err != nil {
			return nil, err
		}
		operands = append(operands, operand)
	}
	instr := Instruction{Mnemonic: mnemonic, Operands: operands, Line: lineNo}
	if err := rv64CheckShape(instr); err != nil {
		return nil, err
	}
	return []Instruction{instr}, nil
}

func parseRV64Operand(text, mnemonic string) (Operand, error) {
	if reg, ok := parseRV64Register(text); ok {
		return reg, nil
	}
	if open := strings.IndexByte(text, '('); open >= 0 && strings.HasSuffix(text, ")") {
		base, ok := parseRV64Register(text[open+1 : len(text)-1])
		if !ok {
			return nil, fmt.Errorf("bad memory base in %q", text)
		}
		offset := int64(0)
		if open > 0 {
			value, err := parseImmediate(strings.TrimPrefix(text[:open], "#"))
			if err != nil {
				return nil, fmt.Errorf("bad memory offset in %q", text)
			}
			offset = value
		}
		return Memory{Base: base, Offset: offset, Mode: MemOffset}, nil
	}
	if value, err := parseImmediate(strings.TrimPrefix(text, "#")); err == nil {
		return Immediate{Value: value}, nil
	}
	if _, isMode := rv64RoundingModes[strings.ToLower(text)]; isMode && rv64FloatShapes[mnemonic] != "" {
		return Option{Name: strings.ToLower(text)}, nil
	}
	if mnemonic == "vsetvli" || mnemonic == "vsetivli" {
		lower := strings.ToLower(text)
		if _, isSEW := rv64VTypeSEW[lower]; isSEW || rv64VTypeLMUL[lower] != 0 || lower == "m1" || rv64VTypePolicy[lower] {
			return Option{Name: lower}, nil
		}
	}
	if isRV64Label(text) {
		return Symbol{Name: text}, nil
	}
	return nil, fmt.Errorf("unrecognized operand %q", text)
}

func isRV64Label(text string) bool {
	if text == "" {
		return false
	}
	for i, r := range text {
		if r == '_' || r == '.' || (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || (i > 0 && r >= '0' && r <= '9') {
			continue
		}
		return false
	}
	return true
}

// rv64CheckShape validates operand shapes per mnemonic, so every later
// phase may index operands by position.
func rv64CheckShape(instr Instruction) error {
	ops := instr.Operands
	is := func(i int, kind string) bool {
		if i >= len(ops) {
			return false
		}
		switch ops[i].(type) {
		case Register:
			return kind == "r"
		case Immediate:
			return kind == "i"
		case Memory:
			return kind == "m"
		case Symbol:
			return kind == "l"
		}
		return false
	}
	shape := func(kinds ...string) error {
		if len(ops) != len(kinds) {
			return fmt.Errorf("%s takes %d operands, got %d", instr.Mnemonic, len(kinds), len(ops))
		}
		for i, kind := range kinds {
			if !is(i, kind) {
				return fmt.Errorf("%s: operand %d must be a %s", instr.Mnemonic, i+1, map[string]string{"r": "register", "i": "immediate", "m": "memory operand imm(base)", "l": "label"}[kind])
			}
		}
		return nil
	}
	name := instr.Mnemonic
	if shape, isFloat := rv64FloatShapes[name]; isFloat {
		return rv64CheckFloatShape(instr, shape)
	}
	if shape, isVector := rv64VectorShapes[name]; isVector {
		return rv64CheckVectorShape(instr, shape)
	}
	if width, isFloat := rv64FloatLoads[name]; isFloat || rv64FloatStores[name] != 0 {
		_ = width
		if len(ops) != 2 || !is(1, "m") {
			return fmt.Errorf("%s takes a floating-point register and a memory operand imm(base)", name)
		}
		if r, isReg := ops[0].(Register); !isReg || r.Class != ClassRV64F {
			return fmt.Errorf("%s: operand 1 must be a floating-point register", name)
		}
		return nil
	}
	switch {
	case name == "add" || name == "sub" || name == "and" || name == "or" || name == "xor" || name == "sll" || name == "srl" || name == "sra" || name == "slt" || name == "sltu" ||
		name == "addw" || name == "subw" || name == "sllw" || name == "srlw" || name == "sraw" || name == "mul" || name == "mulh" || name == "mulhsu" || name == "mulhu" || name == "div" || name == "divu" || name == "rem" || name == "remu" ||
		name == "mulw" || name == "divw" || name == "divuw" || name == "remw" || name == "remuw":
		return shape("r", "r", "r")
	case name == "addi" || name == "andi" || name == "ori" || name == "xori" || name == "slti" || name == "sltiu" || name == "slli" || name == "srli" || name == "srai" || name == "addiw" || name == "slliw" || name == "srliw" || name == "sraiw":
		return shape("r", "r", "i")
	case name == "lui" || name == "li":
		return shape("r", "i")
	case name == "auipc":
		return shape("r", "i")
	case name == "call":
		return shape("l")
	case name == "mv" || name == "not" || name == "neg" || name == "negw" || name == "sext.w":
		return shape("r", "r")
	case rv64Loads[name] != 0 || rv64Stores[name] != 0:
		return shape("r", "m")
	case rv64Branches[name]:
		return shape("r", "r", "l")
	case name == "beqz" || name == "bnez" || name == "bgez" || name == "bltz" || name == "blez" || name == "bgtz":
		return shape("r", "l")
	case name == "jal":
		if len(ops) == 1 && is(0, "l") {
			return nil
		}
		return shape("r", "l")
	case name == "jalr":
		if len(ops) == 1 && is(0, "r") {
			return nil
		}
		return shape("r", "m")
	case name == "j":
		return shape("l")
	case name == "jr":
		return shape("r")
	case name == "ret" || name == "nop" || name == "ecall" || name == "ebreak" || name == "fence":
		if len(ops) != 0 {
			return fmt.Errorf("%s takes no operands", name)
		}
		return nil
	}
	return fmt.Errorf("instruction %s is not admitted by the RV64 checker", name)
}

// rv64CheckFloatShape validates an F/D instruction's operands against its
// shape: f a floating-point register, x an integer register, r an
// optional trailing rounding mode.
func rv64CheckFloatShape(instr Instruction, shape string) error {
	ops := instr.Operands
	required := strings.TrimSuffix(shape, "r")
	optionalMode := strings.HasSuffix(shape, "r")
	if len(ops) < len(required) || len(ops) > len(required)+map[bool]int{true: 1, false: 0}[optionalMode] {
		return fmt.Errorf("%s takes %d operands (and an optional rounding mode), got %d", instr.Mnemonic, len(required), len(ops))
	}
	for i, kind := range required {
		reg, isReg := ops[i].(Register)
		switch kind {
		case 'f':
			if !isReg || reg.Class != ClassRV64F {
				return fmt.Errorf("%s: operand %d must be a floating-point register", instr.Mnemonic, i+1)
			}
		case 'x':
			if !isReg || (reg.Class != ClassRV64X && reg.Class != ClassSP) {
				return fmt.Errorf("%s: operand %d must be an integer register", instr.Mnemonic, i+1)
			}
		}
	}
	if len(ops) > len(required) {
		if _, isMode := ops[len(ops)-1].(Option); !isMode {
			return fmt.Errorf("%s: the last operand must be a rounding mode (rne, rtz, rdn, rup, rmm, dyn)", instr.Mnemonic)
		}
	}
	return nil
}

// rv64CheckVectorShape validates a vector instruction's operands against
// its shape. The vtype of vsetvli/vsetivli is spelled in full — element
// width, LMUL, tail policy, mask policy — so the configuration the checker
// tracks is the one the author wrote, not an assembler default.
func rv64CheckVectorShape(instr Instruction, shape string) error {
	ops := instr.Operands
	if len(ops) != len(shape) {
		return fmt.Errorf("%s takes %d operands, got %d", instr.Mnemonic, len(shape), len(ops))
	}
	for i, kind := range shape {
		switch kind {
		case 'v':
			if reg, isReg := ops[i].(Register); !isReg || reg.Class != ClassRV64V {
				return fmt.Errorf("%s: operand %d must be a vector register", instr.Mnemonic, i+1)
			}
		case 'x':
			if reg, isReg := ops[i].(Register); !isReg || (reg.Class != ClassRV64X && reg.Class != ClassSP) {
				return fmt.Errorf("%s: operand %d must be an integer register", instr.Mnemonic, i+1)
			}
		case 'i':
			if imm, isImm := ops[i].(Immediate); !isImm || imm.Value < 0 || imm.Value > 31 {
				return fmt.Errorf("%s: operand %d must be an immediate vector length 0..31", instr.Mnemonic, i+1)
			}
		case 'm':
			if mem, isMem := ops[i].(Memory); !isMem || mem.Offset != 0 {
				return fmt.Errorf("%s: operand %d must be a memory operand (base) without an offset", instr.Mnemonic, i+1)
			}
		case 'o':
			opt, isOpt := ops[i].(Option)
			if !isOpt {
				return fmt.Errorf("%s: operand %d must be a vtype option (e8|e16|e32|e64, m1|m2|m4|m8|mf2|mf4|mf8, ta|tu, ma|mu)", instr.Mnemonic, i+1)
			}
			position := i - (len(shape) - 4)
			ok := false
			switch position {
			case 0:
				_, ok = rv64VTypeSEW[opt.Name]
			case 1:
				_, ok = rv64VTypeLMUL[opt.Name]
			case 2:
				ok = opt.Name == "ta" || opt.Name == "tu"
			case 3:
				ok = opt.Name == "ma" || opt.Name == "mu"
			}
			if !ok {
				return fmt.Errorf("%s: the vtype is spelled `e*, m*, ta|tu, ma|mu` in that order (operand %d is %s)", instr.Mnemonic, i+1, opt.Name)
			}
		}
	}
	if instr.Mnemonic == "vmerge.vvm" {
		if mask := ops[3].(Register); mask.Num != 0 {
			return fmt.Errorf("vmerge.vvm takes its mask from v0")
		}
	}
	return nil
}

// rv64Base rewrites a pseudo-instruction to its base spelling (docs/spec/
// 94-assembler.md §9): the encoder and the verifier see base instructions.
func rv64Base(instr Instruction) Instruction {
	zero := Register{Text: "zero", Class: ClassRV64X, Num: 0, Lane: -1}
	ra := Register{Text: "ra", Class: ClassRV64X, Num: 1, Lane: -1}
	ops := instr.Operands
	out := instr
	switch instr.Mnemonic {
	case "mv":
		out.Mnemonic, out.Operands = "addi", []Operand{ops[0], ops[1], Immediate{Value: 0}}
	case "not":
		out.Mnemonic, out.Operands = "xori", []Operand{ops[0], ops[1], Immediate{Value: -1}}
	case "neg":
		out.Mnemonic, out.Operands = "sub", []Operand{ops[0], zero, ops[1]}
	case "negw":
		out.Mnemonic, out.Operands = "subw", []Operand{ops[0], zero, ops[1]}
	case "sext.w":
		out.Mnemonic, out.Operands = "addiw", []Operand{ops[0], ops[1], Immediate{Value: 0}}
	case "nop":
		out.Mnemonic, out.Operands = "addi", []Operand{zero, zero, Immediate{Value: 0}}
	case "j":
		out.Mnemonic, out.Operands = "jal", []Operand{zero, ops[0]}
	case "jr":
		out.Mnemonic, out.Operands = "jalr", []Operand{zero, Memory{Base: ops[0].(Register), Mode: MemOffset}}
	case "ret":
		out.Mnemonic, out.Operands = "jalr", []Operand{zero, Memory{Base: ra, Mode: MemOffset}}
	case "beqz":
		out.Mnemonic, out.Operands = "beq", []Operand{ops[0], zero, ops[1]}
	case "bnez":
		out.Mnemonic, out.Operands = "bne", []Operand{ops[0], zero, ops[1]}
	case "bgez":
		out.Mnemonic, out.Operands = "bge", []Operand{ops[0], zero, ops[1]}
	case "bltz":
		out.Mnemonic, out.Operands = "blt", []Operand{ops[0], zero, ops[1]}
	case "blez":
		out.Mnemonic, out.Operands = "bge", []Operand{zero, ops[0], ops[1]}
	case "bgtz":
		out.Mnemonic, out.Operands = "blt", []Operand{zero, ops[0], ops[1]}
	case "jal":
		if len(ops) == 1 {
			out.Operands = []Operand{ra, ops[0]}
		}
	case "jalr":
		if len(ops) == 1 {
			out.Operands = []Operand{ra, Memory{Base: ops[0].(Register), Mode: MemOffset}}
		}
	case "li":
		// A 12-bit immediate is addi from zero; a 32-bit one is lui plus
		// addiw and takes two words (expanded by the encoder).
		value := ops[1].(Immediate).Value
		if value >= -2048 && value <= 2047 {
			out.Mnemonic, out.Operands = "addi", []Operand{ops[0], zero, Immediate{Value: value}}
		}
	}
	return out
}
