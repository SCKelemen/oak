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
