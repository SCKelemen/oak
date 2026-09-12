package asm

import (
	"fmt"
	"strconv"
	"strings"
)

// CPrelude is emitted once before any asm block: the symbol macro applies
// the target's user-label prefix ("_" on Mach-O, "" on ELF) so the same
// generated C links on both.
const CPrelude = `/* asm units (docs/spec/94-assembler.md): top-level assembly blocks;
   OAK_ASM_SYMBOL applies the target's user-label prefix */
#define OAK_ASM_STR_(x) #x
#define OAK_ASM_STR(x) OAK_ASM_STR_(x)
#define OAK_ASM_SYMBOL(name) OAK_ASM_STR(__USER_LABEL_PREFIX__) #name
`

// EmitCExtern is EmitC's counterpart when the unit is encoded by the Oak
// assembler into a companion object (docs/spec/94-assembler.md §9): the C
// keeps only the prototype the declaration emitted and, without an Oak
// fallback body, fails closed off AArch64.
func EmitCExtern(fn *Function, cSymbol string) string {
	var b strings.Builder
	fmt.Fprintf(&b, "/* asm unit: %s — encoded by the Oak assembler into the companion object as %s */\n", fn.Name, cSymbol)
	if !fn.Fallback {
		fmt.Fprintf(&b, "#if !(%s) || defined(OAK_PORTABLE_INTRINSICS)\n", archCondition(fn))
		fmt.Fprintf(&b, "#error \"asm unit %s requires %s (no Oak fallback body declared)\"\n", fn.Name, archName(fn))
		b.WriteString("#endif\n")
	}
	b.WriteString("\n")
	return b.String()
}

// EmitC renders one checked asm function as a top-level GNU assembly block
// under the C symbol the Oak declaration's prototype uses. Non-AArch64
// targets fail closed with #error: an asm unit is never silently stubbed.
func EmitC(fn *Function, cSymbol string, symbolFor func(string) string) string {
	var b strings.Builder
	fmt.Fprintf(&b, "/* asm unit: %s */\n", fn.Name)
	fmt.Fprintf(&b, "#if (%s) && !defined(OAK_PORTABLE_INTRINSICS)\n", archCondition(fn))
	b.WriteString("__asm__(\n")
	b.WriteString("  \"  .text\\n\"\n")
	align := fn.Align
	if align == 0 {
		align = 4
	}
	fmt.Fprintf(&b, "  \"  .balign %d\\n\"\n", align)
	if usesScalableFile(fn) {
		// The host assembler must accept SVE/SME spellings (the Oak
		// assembler needs no such directive on the native path).
		for _, ext := range []string{"sme", "sme2", "sme-f64f64", "sme-i16i64"} {
			fmt.Fprintf(&b, "  \"  .arch_extension %s\\n\"\n", ext)
		}
	}
	for _, ext := range extensionDirectives(fn) {
		// The host assembler must accept the CRC and SHA-2 spellings on
		// toolchains whose default -march lacks them (GNU as on Linux);
		// Apple's and the Oak assembler's native path need no directive.
		fmt.Fprintf(&b, "  \"  .arch_extension %s\\n\"\n", ext)
	}
	fmt.Fprintf(&b, "  \"  .globl \" OAK_ASM_SYMBOL(%s) \"\\n\"\n", cSymbol)
	fmt.Fprintf(&b, "  OAK_ASM_SYMBOL(%s) \":\\n\"\n", cSymbol)
	// Labels render as GNU numeric local labels (1:, branches 1b/1f), which
	// are assembler-local on both Mach-O and ELF; .L names are external on
	// Mach-O.
	numbers := map[string]int{}
	for _, item := range fn.Items {
		if label, ok := item.(Label); ok {
			numbers[label.Name] = len(numbers) + 1
		}
	}
	defined := map[string]bool{}
	first := true
	for _, item := range fn.Items {
		switch it := item.(type) {
		case Label:
			defined[it.Name] = true
			fmt.Fprintf(&b, "  \"%d:\\n\"\n", numbers[it.Name])
		case Align:
			if first && it.Bytes == fn.Align {
				// The function-entry alignment was already applied.
				first = false
				continue
			}
			fmt.Fprintf(&b, "  \"  .balign %d\\n\"\n", it.Bytes)
		case Instruction:
			fmt.Fprintf(&b, "  \"  %s\\n\"\n", renderInstruction(fn, it, symbolFor, numbers, defined))
		}
		first = false
	}
	b.WriteString(");\n")
	if fn.Fallback {
		// The Oak body is emitted by the ordinary function emitter under the
		// complementary condition.
		b.WriteString("#endif\n\n")
		return b.String()
	}
	b.WriteString("#else\n")
	fmt.Fprintf(&b, "#error \"asm unit %s requires %s (no Oak fallback body declared)\"\n", fn.Name, archName(fn))
	b.WriteString("#endif\n\n")
	return b.String()
}

// archCondition is the preprocessor test selecting the unit's lane: the
// C toolchain's target must be the lane's architecture, else the Oak
// fallback body (or #error) applies.
func archCondition(fn *Function) string { return ArchCondition(fn.Arch) }

// ArchCondition is the preprocessor test for a lane's architecture: the
// asm unit applies under it, the Oak fallback body under its negation.
func ArchCondition(arch string) string {
	if arch == ArchRV64 {
		return "defined(__riscv) && (__riscv_xlen == 64)"
	}
	return "defined(__aarch64__)"
}

func archName(fn *Function) string {
	if fn.Arch == ArchRV64 {
		return "an RV64 target"
	}
	return "an AArch64 target"
}

// extensionDirectives lists the `.arch_extension` names a unit's
// instructions need beyond the base architecture: `crc` for the CRC-32
// steps and `sha2` for the SHA-256 rounds (FEAT_CRC32, FEAT_SHA256).
func extensionDirectives(fn *Function) []string {
	var exts []string
	seen := map[string]bool{}
	for _, item := range fn.Items {
		instr, ok := item.(Instruction)
		if !ok {
			continue
		}
		ext := ""
		switch {
		case strings.HasPrefix(instr.Mnemonic, "crc32"):
			ext = "crc"
		case strings.HasPrefix(instr.Mnemonic, "sha256"):
			ext = "sha2"
		}
		if ext != "" && !seen[ext] {
			seen[ext] = true
			exts = append(exts, ext)
		}
	}
	return exts
}

// usesScalableFile reports a function with SVE/SME instructions.
func usesScalableFile(fn *Function) bool {
	for _, item := range fn.Items {
		if instr, ok := item.(Instruction); ok {
			spec := instructionTable[instr.Mnemonic]
			if spec.tableForms && (len(spec.forms) == 0 || usesScalable(instr.Operands)) {
				return true
			}
		}
	}
	return false
}

// String spells an instruction as `.oakasm` text with symbols by name.
func (instr Instruction) String() string {
	mnemonic := instr.Mnemonic
	if mnemonic == "b." {
		mnemonic = "b." + instr.Cond
	}
	if len(instr.Operands) == 0 {
		return mnemonic
	}
	parts := make([]string, 0, len(instr.Operands))
	for _, operand := range instr.Operands {
		if sym, isSym := operand.(Symbol); isSym {
			parts = append(parts, sym.Name)
			continue
		}
		parts = append(parts, renderOperand(operand, func(s string) string { return s }, nil, nil))
	}
	return mnemonic + " " + strings.Join(parts, ", ")
}

func renderInstruction(fn *Function, instr Instruction, symbolFor func(string) string, numbers map[string]int, defined map[string]bool) string {
	if fn.Arch == ArchRV64 {
		return renderRV64Instruction(instr, symbolFor, numbers, defined)
	}
	mnemonic := instr.Mnemonic
	if mnemonic == "b." {
		mnemonic = "b." + instr.Cond
	}
	if len(instr.Operands) == 0 {
		return mnemonic
	}
	parts := make([]string, 0, len(instr.Operands))
	for _, operand := range instr.Operands {
		parts = append(parts, renderOperand(operand, symbolFor, numbers, defined))
	}
	return mnemonic + " " + strings.Join(parts, ", ")
}

func renderOperand(operand Operand, symbolFor func(string) string, numbers map[string]int, defined map[string]bool) string {
	switch o := operand.(type) {
	case Register:
		return o.Text
	case Immediate:
		if o.Shift != 0 {
			return fmt.Sprintf("#%d, lsl #%d", o.Value, o.Shift)
		}
		return fmt.Sprintf("#%d", o.Value)
	case Shifted, Extended:
		text, _ := renderModified(o)
		return text
	case RegisterList:
		names := make([]string, len(o.Regs))
		for i, reg := range o.Regs {
			names[i] = reg.Text
		}
		return "{" + strings.Join(names, ", ") + "}"
	case TileSlice:
		if o.Listed {
			return "{" + o.Text + "}"
		}
		return o.Text
	case FloatImmediate:
		text := strconv.FormatFloat(o.Value, 'f', -1, 64)
		if !strings.ContainsAny(text, ".eE") {
			text += ".0"
		}
		return "#" + text
	case Memory:
		if o.Index != nil {
			extend := o.Extend
			if extend == "" {
				extend = "uxtw"
			}
			if o.Shift == 0 {
				if extend == "lsl" {
					return fmt.Sprintf("[%s, %s]", o.Base.Text, o.Index.Text)
				}
				return fmt.Sprintf("[%s, %s, %s]", o.Base.Text, o.Index.Text, extend)
			}
			return fmt.Sprintf("[%s, %s, %s #%d]", o.Base.Text, o.Index.Text, extend, o.Shift)
		}
		switch o.Mode {
		case MemPreIndex:
			return fmt.Sprintf("[%s, #%d]!", o.Base.Text, o.Offset)
		case MemPostIndex:
			return fmt.Sprintf("[%s], #%d", o.Base.Text, o.Offset)
		}
		if o.MulVL {
			return fmt.Sprintf("[%s, #%d, mul vl]", o.Base.Text, o.Offset)
		}
		if o.Offset == 0 {
			return fmt.Sprintf("[%s]", o.Base.Text)
		}
		return fmt.Sprintf("[%s, #%d]", o.Base.Text, o.Offset)
	case Symbol:
		// Local labels are function-scoped numeric labels (backward `b`
		// when already defined, forward `f` otherwise); anything else is an
		// Oak function reached through its C symbol.
		if number, isLabel := numbers[o.Name]; isLabel {
			if defined[o.Name] {
				return fmt.Sprintf("%db", number)
			}
			return fmt.Sprintf("%df", number)
		}
		return "\" OAK_ASM_SYMBOL(" + symbolFor(o.Name) + ") \""
	case SysReg:
		return o.Name
	case Option:
		if o.Mul != 0 {
			return fmt.Sprintf("%s, mul #%d", o.Name, o.Mul)
		}
		return o.Name
	case Condition:
		return o.Code
	}
	return "?"
}

// renderRV64Instruction spells an instruction in GNU RISC-V syntax:
// registers by ABI name, bare immediates, `imm(base)` memory, labels as
// numeric local labels, and other symbols through symbolFor.
func renderRV64Instruction(instr Instruction, symbolFor func(string) string, numbers map[string]int, defined map[string]bool) string {
	if len(instr.Operands) == 0 {
		return instr.Mnemonic
	}
	parts := make([]string, 0, len(instr.Operands))
	for _, operand := range instr.Operands {
		parts = append(parts, renderRV64Operand(operand, symbolFor, numbers, defined))
	}
	return instr.Mnemonic + " " + strings.Join(parts, ", ")
}

func renderRV64Operand(operand Operand, symbolFor func(string) string, numbers map[string]int, defined map[string]bool) string {
	switch o := operand.(type) {
	case Register:
		return o.Text
	case Immediate:
		return fmt.Sprintf("%d", o.Value)
	case Memory:
		return fmt.Sprintf("%d(%s)", o.Offset, o.Base.Text)
	case Symbol:
		if number, isLabel := numbers[o.Name]; isLabel {
			if defined[o.Name] {
				return fmt.Sprintf("%db", number)
			}
			return fmt.Sprintf("%df", number)
		}
		if symbolFor == nil {
			return o.Name
		}
		return "\" OAK_ASM_SYMBOL(" + symbolFor(o.Name) + ") \""
	}
	return "?"
}
