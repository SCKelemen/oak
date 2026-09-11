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
		b.WriteString("#if !defined(__aarch64__) || defined(OAK_PORTABLE_INTRINSICS)\n")
		fmt.Fprintf(&b, "#error \"asm unit %s requires an AArch64 target (no Oak fallback body declared)\"\n", fn.Name)
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
	b.WriteString("#if defined(__aarch64__) && !defined(OAK_PORTABLE_INTRINSICS)\n")
	b.WriteString("__asm__(\n")
	b.WriteString("  \"  .text\\n\"\n")
	align := fn.Align
	if align == 0 {
		align = 4
	}
	fmt.Fprintf(&b, "  \"  .balign %d\\n\"\n", align)
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
	fmt.Fprintf(&b, "#error \"asm unit %s requires an AArch64 target (no Oak fallback body declared)\"\n", fn.Name)
	b.WriteString("#endif\n\n")
	return b.String()
}

func renderInstruction(fn *Function, instr Instruction, symbolFor func(string) string, numbers map[string]int, defined map[string]bool) string {
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
		return o.Name
	case Condition:
		return o.Code
	}
	return "?"
}
