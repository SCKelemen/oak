// Package asm implements Oak's typed abstract assembler
// (docs/spec/94-assembler.md): parsing of `.oakasm` translation units,
// the AArch64 instruction table, the seam checker (bindings, widths,
// clobbers, flags dataflow, frame bounds, alignment extents, privilege),
// and emission as top-level assembly blocks in the C backend.
//
// Assembly never appears inline in Oak bodies. An Oak file declares the
// typed interface (a definition-less signature); the unit repeats the
// identical signature and supplies the instruction block. What the checker
// enforces at the seams is checked, not trusted; the author's algorithm
// inside a straight-line body is the remaining trust (spec §5).
package asm

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Unit is one parsed `.oakasm` translation unit.
type Unit struct {
	Path      string
	Functions []*Function
}

// Function is one asm function: its declared signature (parsed with the
// Oak parser, so identity with the Oak declaration is a structural
// comparison) and its instruction block.
type Function struct {
	Name      string
	Signature *ast.FunctionStatement
	Line      int
	Items     []Item
	// Directives collected from the block.
	Bindings []Binding
	Clobbers []Register
	Frame    int64 // declared stack frame in bytes, 0 when none
	System   bool  // capability for mrs/msr/eret
	Align    int64 // function entry alignment, 0 for the default
	// Fallback marks that the Oak declaration also carries an Oak body: the
	// backend emits it for non-AArch64 targets (and under
	// OAK_PORTABLE_INTRINSICS), so the asm and the Oak body are two
	// realizations of one signature.
	Fallback bool
}

// Item is one line of the block: a label, an align directive, or an
// instruction. Directives (bind/clobber/frame/system) are collected on the
// Function, not kept as items.
type Item interface{ itemLine() int }

type Label struct {
	Name string
	Line int
}

type Align struct {
	Bytes int64
	Line  int
}

type Instruction struct {
	Mnemonic string // lowercase, e.g. "add", "b", "stp"
	Cond     string // condition suffix for b.cond ("ne", "eq", ...), else ""
	Operands []Operand
	Line     int
}

func (l Label) itemLine() int       { return l.Line }
func (a Align) itemLine() int       { return a.Line }
func (i Instruction) itemLine() int { return i.Line }

// Binding pins a parameter to its contract register: bind w0 = left. A
// span or view parameter binds its pair: bind x0, w1 = frame (base pointer,
// then the 32-bit length; the upper half of x1 is padding and never read).
type Binding struct {
	Register Register
	Length   *Register
	Param    string
	Line     int
}

// Operand kinds.
type Operand interface{ operandKind() string }

// Register is a parsed register operand.
type Register struct {
	Text  string // as written: "x0", "w5", "sp", "lr", "v3"
	Class RegClass
	Num   int // physical register number for X/W (0..30), V (0..31); -1 for SP; 31 for zero registers
}

type Immediate struct{ Value int64 }

// Memory is an sp-relative or register-relative access: [base, #off],
// [base, #off]! (pre-index), [base], #off (post-index).
type Memory struct {
	Base   Register
	Offset int64
	Mode   MemMode
}

type MemMode int

const (
	MemOffset MemMode = iota
	MemPreIndex
	MemPostIndex
)

// Symbol names a label inside the function or an Oak-visible function.
type Symbol struct{ Name string }

// SysReg names a system register operand of mrs/msr.
type SysReg struct{ Name string }

// Option is a barrier option word (sy, ish, ...).
type Option struct{ Name string }

// Condition is the condition-code operand of csel/cset (eq, lo, ge, ...).
type Condition struct{ Code string }

func (Condition) operandKind() string { return "condition" }
func (Register) operandKind() string  { return "register" }
func (Immediate) operandKind() string { return "immediate" }
func (Memory) operandKind() string    { return "memory" }
func (Symbol) operandKind() string    { return "symbol" }
func (SysReg) operandKind() string    { return "sysreg" }
func (Option) operandKind() string    { return "option" }

// RegClass is the register type of docs/spec/94-assembler.md §3.
type RegClass int

const (
	ClassX  RegClass = iota // arm64.X — 64-bit general
	ClassW                  // arm64.W — 32-bit view
	ClassV                  // arm64.V — 128-bit vector
	ClassSP                 // arm64.SP — the stack pointer
)

func (c RegClass) String() string {
	switch c {
	case ClassX:
		return "arm64.X"
	case ClassW:
		return "arm64.W"
	case ClassV:
		return "arm64.V"
	case ClassSP:
		return "arm64.SP"
	}
	return "?"
}

// ZeroRegister reports xzr/wzr (register number 31 in the general file).
func (r Register) ZeroRegister() bool {
	return (r.Class == ClassX || r.Class == ClassW) && r.Num == 31
}

// ParseError is a unit parse failure with a source line.
type ParseError struct {
	Path string
	Line int
	Msg  string
}

func (e *ParseError) Error() string {
	return fmt.Sprintf("%s:%d: %s", e.Path, e.Line, e.Msg)
}

// ParseUnit parses one `.oakasm` unit. The block grammar is line-oriented:
//
//	name: (params) -> Ret = {
//	  bind w0 = left           directives: bind, clobber, frame, system, align
//	  clobber x9, x10
//	  frame 32
//	  system
//	  loop:                    labels
//	  add w0, w0, w1           instructions: mnemonic operands
//	  b.ne loop
//	}
//
// `//` starts a comment. The header signature is parsed by the Oak parser.
func ParseUnit(path, text string) (*Unit, []error) {
	unit := &Unit{Path: path}
	var errs []error
	fail := func(line int, format string, args ...interface{}) {
		errs = append(errs, &ParseError{Path: path, Line: line, Msg: fmt.Sprintf(format, args...)})
	}

	lines := strings.Split(text, "\n")
	var current *Function
	for index, raw := range lines {
		lineNo := index + 1
		line := raw
		if cut := strings.Index(line, "//"); cut >= 0 {
			line = line[:cut]
		}
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		if current == nil {
			if !strings.HasSuffix(line, "{") {
				fail(lineNo, "expected an asm function header `name: (params) -> Ret = {`, got %q", line)
				continue
			}
			header := strings.TrimSpace(strings.TrimSuffix(line, "{"))
			header = strings.TrimSpace(strings.TrimSuffix(header, "="))
			signature, err := parseSignature(header)
			if err != nil {
				fail(lineNo, "asm function header: %v", err)
				continue
			}
			current = &Function{Name: signature.Name.Value, Signature: signature, Line: lineNo}
			continue
		}

		if line == "}" {
			if usesOperandStack(current) {
				if err := desugarOperandStack(current); err != nil {
					fail(lineNo, "%v", err)
				}
			}
			unit.Functions = append(unit.Functions, current)
			current = nil
			continue
		}

		if strings.HasSuffix(line, ":") && !strings.ContainsAny(line, " \t,") {
			current.Items = append(current.Items, Label{Name: strings.TrimSuffix(line, ":"), Line: lineNo})
			continue
		}

		fields := splitFields(line)
		head := strings.ToLower(fields[0])
		switch head {
		case "bind":
			// bind w0 = left  |  bind x0, w1 = frame
			switch {
			case len(fields) == 4 && fields[2] == "=":
				reg, ok := parseRegister(fields[1])
				if !ok {
					fail(lineNo, "bind: unknown register %q", fields[1])
					continue
				}
				current.Bindings = append(current.Bindings, Binding{Register: reg, Param: fields[3], Line: lineNo})
			case len(fields) == 5 && fields[3] == "=":
				base, okBase := parseRegister(fields[1])
				length, okLen := parseRegister(fields[2])
				if !okBase || !okLen {
					fail(lineNo, "bind: unknown register in pair %q, %q", fields[1], fields[2])
					continue
				}
				current.Bindings = append(current.Bindings, Binding{Register: base, Length: &length, Param: fields[4], Line: lineNo})
			default:
				fail(lineNo, "bind takes the form `bind <register> = <parameter>` or `bind <base>, <length> = <span>`")
				continue
			}
		case "clobber":
			for _, name := range fields[1:] {
				reg, ok := parseRegister(name)
				if !ok {
					fail(lineNo, "clobber: unknown register %q", name)
					continue
				}
				current.Clobbers = append(current.Clobbers, reg)
			}
		case "frame":
			if len(fields) != 2 {
				fail(lineNo, "frame takes one byte count")
				continue
			}
			bytes, err := strconv.ParseInt(fields[1], 10, 64)
			if err != nil || bytes <= 0 || bytes%16 != 0 {
				fail(lineNo, "frame size must be a positive multiple of 16 bytes")
				continue
			}
			current.Frame = bytes
		case "system":
			current.System = true
		case "align":
			if len(fields) != 2 {
				fail(lineNo, "align takes one byte count")
				continue
			}
			bytes, err := strconv.ParseInt(fields[1], 10, 64)
			if err != nil || bytes < 4 || bytes&(bytes-1) != 0 {
				fail(lineNo, "align must be a power of two of at least 4")
				continue
			}
			if len(current.Items) == 0 && current.Align == 0 {
				current.Align = bytes
			}
			current.Items = append(current.Items, Align{Bytes: bytes, Line: lineNo})
		default:
			instr, err := parseInstruction(fields, lineNo)
			if err != nil {
				fail(lineNo, "%v", err)
				continue
			}
			current.Items = append(current.Items, instr)
		}
	}
	if current != nil {
		fail(len(lines), "asm function %s: missing closing `}`", current.Name)
	}
	return unit, errs
}

// parseSignatureWithBody parses an Oak function declaration that may carry
// a body — the specification side of §8 verification in tests.
func parseSignatureWithBody(source string) (*ast.FunctionStatement, error) {
	p := parser.New(layout.New(scanner.New(source)))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		return nil, fmt.Errorf("%s", strings.Join(errors, "; "))
	}
	if program == nil || len(program.Statements) != 1 {
		return nil, fmt.Errorf("expected exactly one function declaration")
	}
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok || fn.Name == nil {
		return nil, fmt.Errorf("not a function declaration")
	}
	return fn, nil
}

// parseSignature runs the Oak parser over the header so the asm side and
// the Oak declaration are compared structurally, never textually.
func parseSignature(header string) (*ast.FunctionStatement, error) {
	p := parser.New(layout.New(scanner.New(header)))
	program := p.ParseProgram()
	if errors := p.Errors(); len(errors) != 0 {
		return nil, fmt.Errorf("%s", strings.Join(errors, "; "))
	}
	if program == nil || len(program.Statements) != 1 {
		return nil, fmt.Errorf("header must be exactly one function signature")
	}
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok || fn.Name == nil {
		return nil, fmt.Errorf("header is not a function signature")
	}
	if fn.Body != nil {
		return nil, fmt.Errorf("header must not carry an Oak body")
	}
	return fn, nil
}

// splitFields splits an instruction line on whitespace and commas while
// keeping bracketed memory operands intact: "stp x0, x1, [sp, #-16]!" ->
// ["stp", "x0", "x1", "[sp, #-16]!"].
func splitFields(line string) []string {
	var fields []string
	var current strings.Builder
	depth := 0
	flush := func() {
		if current.Len() > 0 {
			fields = append(fields, current.String())
			current.Reset()
		}
	}
	for _, r := range line {
		switch {
		case r == '[':
			depth++
			current.WriteRune(r)
		case r == ']':
			depth--
			current.WriteRune(r)
		case (r == ',' || r == ' ' || r == '\t') && depth == 0:
			flush()
		default:
			current.WriteRune(r)
		}
	}
	flush()
	return fields
}

func parseInstruction(fields []string, line int) (Instruction, error) {
	mnemonic := strings.ToLower(fields[0])
	instr := Instruction{Mnemonic: mnemonic, Line: line}
	if strings.HasPrefix(mnemonic, "b.") {
		instr.Mnemonic = "b."
		instr.Cond = strings.TrimPrefix(mnemonic, "b.")
		if !conditionCodes[instr.Cond] {
			return instr, fmt.Errorf("unknown condition code %q", instr.Cond)
		}
	}
	// `push` belongs to the operand-stack shorthand (asm/stack.go): its one
	// operand is a parameter name or an immediate, resolved at desugaring.
	if instr.Mnemonic == "push" {
		if len(fields) != 2 {
			return instr, fmt.Errorf("push takes one parameter name or #immediate")
		}
		if fields[1][0] == '#' {
			value, err := parseImmediate(fields[1][1:])
			if err != nil {
				return instr, err
			}
			instr.Operands = []Operand{Immediate{Value: value}}
		} else {
			instr.Operands = []Operand{Symbol{Name: fields[1]}}
		}
		return instr, nil
	}
	spec, known := instructionTable[instr.Mnemonic]
	if !known {
		return instr, fmt.Errorf("unknown instruction %q (not in the v1 AArch64 table)", mnemonic)
	}
	for i := 1; i < len(fields); i++ {
		operand, err := parseOperand(fields[i], i-1, spec)
		if err != nil {
			return instr, err
		}
		// Post-index addressing arrives as two fields: "[sp]" then "#16".
		if imm, isImm := operand.(Immediate); isImm && len(instr.Operands) > 0 {
			if mem, isMem := instr.Operands[len(instr.Operands)-1].(Memory); isMem && mem.Mode == MemOffset && mem.Offset == 0 {
				mem.Mode = MemPostIndex
				mem.Offset = imm.Value
				instr.Operands[len(instr.Operands)-1] = mem
				continue
			}
		}
		instr.Operands = append(instr.Operands, operand)
	}
	return instr, nil
}

func parseOperand(text string, position int, spec instructionSpec) (Operand, error) {
	if strings.HasPrefix(text, "#") {
		value, err := parseImmediate(text[1:])
		if err != nil {
			return nil, err
		}
		return Immediate{Value: value}, nil
	}
	if strings.HasPrefix(text, "[") {
		return parseMemory(text)
	}
	if reg, ok := parseRegister(text); ok {
		return reg, nil
	}
	lower := strings.ToLower(text)
	if spec.sysregOperand == position {
		return SysReg{Name: lower}, nil
	}
	if spec.branch != branchNone {
		return Symbol{Name: text}, nil
	}
	if spec.barrier {
		return Option{Name: lower}, nil
	}
	if spec.readsFlags && conditionCodes[lower] {
		return Condition{Code: lower}, nil
	}
	return nil, fmt.Errorf("unrecognized operand %q", text)
}

func parseImmediate(text string) (int64, error) {
	negative := strings.HasPrefix(text, "-")
	text = strings.TrimPrefix(text, "-")
	var value int64
	var err error
	if strings.HasPrefix(strings.ToLower(text), "0x") {
		value, err = strconv.ParseInt(text[2:], 16, 64)
	} else {
		value, err = strconv.ParseInt(text, 10, 64)
	}
	if err != nil {
		return 0, fmt.Errorf("bad immediate %q", text)
	}
	if negative {
		value = -value
	}
	return value, nil
}

// parseMemory parses [base], [base, #off], [base, #off]! and the
// post-index form "[base]" followed by ", #off" (already joined by
// splitFields as "[sp]" then "#16" — handled by parseInstruction's caller
// leaving two fields; we rejoin here when the text ends with "]" and the
// caller passes the trailing immediate separately).
func parseMemory(text string) (Operand, error) {
	pre := strings.HasSuffix(text, "!")
	text = strings.TrimSuffix(text, "!")
	if !strings.HasPrefix(text, "[") || !strings.HasSuffix(text, "]") {
		return nil, fmt.Errorf("bad memory operand %q", text)
	}
	inner := strings.TrimSpace(text[1 : len(text)-1])
	parts := strings.Split(inner, ",")
	base, ok := parseRegister(strings.TrimSpace(parts[0]))
	if !ok {
		return nil, fmt.Errorf("bad memory base %q", parts[0])
	}
	mem := Memory{Base: base}
	if len(parts) == 2 {
		offsetText := strings.TrimSpace(parts[1])
		if !strings.HasPrefix(offsetText, "#") {
			return nil, fmt.Errorf("memory offset must be an immediate, got %q", offsetText)
		}
		offset, err := parseImmediate(offsetText[1:])
		if err != nil {
			return nil, err
		}
		mem.Offset = offset
	} else if len(parts) > 2 {
		return nil, fmt.Errorf("bad memory operand %q", text)
	}
	if pre {
		mem.Mode = MemPreIndex
	}
	return mem, nil
}

// parseRegister recognizes the v1 AArch64 register file.
func parseRegister(text string) (Register, bool) {
	lower := strings.ToLower(text)
	switch lower {
	case "sp":
		return Register{Text: lower, Class: ClassSP, Num: -1}, true
	case "lr":
		return Register{Text: lower, Class: ClassX, Num: 30}, true
	case "xzr":
		return Register{Text: lower, Class: ClassX, Num: 31}, true
	case "wzr":
		return Register{Text: lower, Class: ClassW, Num: 31}, true
	}
	if len(lower) < 2 {
		return Register{}, false
	}
	num, err := strconv.Atoi(lower[1:])
	if err != nil || num < 0 {
		return Register{}, false
	}
	switch lower[0] {
	case 'x':
		if num <= 30 {
			return Register{Text: lower, Class: ClassX, Num: num}, true
		}
	case 'w':
		if num <= 30 {
			return Register{Text: lower, Class: ClassW, Num: num}, true
		}
	case 'v':
		if num <= 31 {
			return Register{Text: lower, Class: ClassV, Num: num}, true
		}
	}
	return Register{}, false
}
