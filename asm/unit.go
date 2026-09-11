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
	Text  string // as written: "x0", "w5", "sp", "lr", "v3", "d1", "v0.4s", "v2.s[1]"
	Class RegClass
	Num   int // physical register number for X/W (0..30), V (0..31); -1 for SP; 31 for zero registers
	// Vec is the vector register's view: a scalar width letter ("b", "h",
	// "s", "d", "q"), an arrangement ("8b", "16b", "4h", "8h", "2s", "4s",
	// "1d", "2d"), or "" for the whole register named as vN. Lane is the
	// element index of a lane reference (v0.s[1]), -1 when none.
	Vec  string
	Lane int
}

// RegisterList is the `{v0.4s, v1.4s}` operand of the structure loads.
type RegisterList struct{ Regs []Register }

// FloatImmediate is `#0.0` and friends (fcmp, fmov).
type FloatImmediate struct{ Value float64 }

func (RegisterList) operandKind() string   { return "register list" }
func (FloatImmediate) operandKind() string { return "float immediate" }

var vectorArrangements = map[string]int{"8b": 8, "16b": 16, "4h": 4, "8h": 8, "2s": 2, "4s": 4, "1d": 1, "2d": 2, "1q": 1}
var scalarVectorWidths = map[byte]int{'b': 1, 'h': 2, 's': 4, 'd': 8, 'q': 16}

// VecBytes is the byte width of a vector-class register view.
func (r Register) VecBytes() int64 {
	if r.Class != ClassV {
		return 0
	}
	if r.Vec == "" {
		return 16
	}
	if lanes, isArrangement := vectorArrangements[r.Vec]; isArrangement {
		return int64(lanes * laneBytes(r.Vec))
	}
	return int64(scalarVectorWidths[r.Vec[0]])
}

// laneBytes is the element width of an arrangement or lane letter.
func laneBytes(arrangement string) int {
	switch arrangement[len(arrangement)-1] {
	case 'b':
		return 1
	case 'h':
		return 2
	case 's':
		return 4
	case 'd':
		return 8
	case 'q':
		return 16
	}
	return 0
}

// Immediate is a constant operand; Shift is the `lsl #16`-style shift of a
// movz/movk/movn immediate (0 when absent).
type Immediate struct {
	Value int64
	Shift int64
}

// Memory is an sp-relative or register-relative access: [base, #off],
// [base, #off]! (pre-index), [base], #off (post-index).
type Memory struct {
	Base   Register
	Offset int64
	Mode   MemMode
	// Index is the scaled register-offset form [base, wI, uxtw #Shift]: the
	// 32-bit index register zero-extended and shifted by Shift (the access
	// size's log2) — how a loop walks a span by element index.
	Index *Register
	Shift int
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
		case r == '{':
			depth++
			current.WriteRune(r)
		case r == '}':
			depth--
			current.WriteRune(r)
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
		// A trailing `lsl #3` / `uxtw` field modifies the operand before it;
		// splitFields separates the kind from its amount, so rejoin them.
		modifier := fields[i]
		if lower := strings.ToLower(modifier); (shiftKinds[lower] || extendKinds[lower]) && i+1 < len(fields) && strings.HasPrefix(fields[i+1], "#") {
			modifier = fields[i] + " " + fields[i+1]
			i++
		}
		if folded, consumed, err := foldModifier(modifier, instr.Operands); err != nil {
			return instr, err
		} else if consumed {
			instr.Operands = folded
			continue
		}
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
		if strings.ContainsAny(text[1:], ".eE") && !strings.HasPrefix(strings.ToLower(text[1:]), "0x") {
			value, err := strconv.ParseFloat(text[1:], 64)
			if err != nil {
				return nil, fmt.Errorf("bad float immediate %q", text)
			}
			return FloatImmediate{Value: value}, nil
		}
		value, err := parseImmediate(text[1:])
		if err != nil {
			return nil, err
		}
		return Immediate{Value: value}, nil
	}
	if strings.HasPrefix(text, "{") && strings.HasSuffix(text, "}") {
		var list RegisterList
		for _, part := range strings.Split(text[1:len(text)-1], ",") {
			reg, ok := parseRegister(strings.TrimSpace(part))
			if !ok || reg.Class != ClassV || reg.Vec == "" || reg.Lane >= 0 {
				return nil, fmt.Errorf("register list %q must hold arranged vector registers", text)
			}
			list.Regs = append(list.Regs, reg)
		}
		if len(list.Regs) < 1 || len(list.Regs) > 4 {
			return nil, fmt.Errorf("register list %q must hold one to four registers", text)
		}
		for _, reg := range list.Regs[1:] {
			if reg.Vec != list.Regs[0].Vec {
				return nil, fmt.Errorf("register list %q mixes arrangements", text)
			}
		}
		return list, nil
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
	if spec.branch != branchNone || formsTakeSymbol(spec, position) {
		return Symbol{Name: text}, nil
	}
	if spec.barrier || formsTakeOption(spec, position) {
		return Option{Name: lower}, nil
	}
	if spec.readsFlags && conditionCodes[lower] {
		return Condition{Code: lower}, nil
	}
	return nil, fmt.Errorf("unrecognized operand %q", text)
}

// formsTakeOption reports whether some legal form of the instruction has an
// option word at the position (prefetch operations, maintenance targets).
func formsTakeOption(spec instructionSpec, position int) bool {
	for _, candidate := range spec.forms {
		if position < len(candidate) && candidate[position] == opOption {
			return true
		}
	}
	return false
}

// formsTakeSymbol reports whether some legal form of a non-branch
// instruction names a label at the position (adr/adrp).
func formsTakeSymbol(spec instructionSpec, position int) bool {
	for _, candidate := range spec.forms {
		if position < len(candidate) && candidate[position] == opSym {
			return true
		}
	}
	return false
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
	} else if len(parts) == 3 {
		// [base, wI, uxtw #s]: a scaled 32-bit index.
		index, ok := parseRegister(strings.TrimSpace(parts[1]))
		if !ok || index.Class != ClassW {
			return nil, fmt.Errorf("memory index must be a w register, got %q", strings.TrimSpace(parts[1]))
		}
		extend := strings.Fields(strings.ToLower(strings.TrimSpace(parts[2])))
		if len(extend) == 0 || extend[0] != "uxtw" || len(extend) > 2 {
			return nil, fmt.Errorf("memory index extension must be `uxtw #s`, got %q", strings.TrimSpace(parts[2]))
		}
		if len(extend) == 2 {
			if !strings.HasPrefix(extend[1], "#") {
				return nil, fmt.Errorf("index shift must be an immediate, got %q", extend[1])
			}
			shift, err := parseImmediate(extend[1][1:])
			if err != nil || shift < 0 || shift > 4 {
				return nil, fmt.Errorf("bad index shift %q", extend[1])
			}
			mem.Shift = int(shift)
		}
		if pre {
			return nil, fmt.Errorf("register-offset addressing has no pre-index form")
		}
		mem.Index = &index
	} else if len(parts) > 3 {
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
	// Vector views: v0.4s (arrangement), v0.s[1] (lane).
	if lower[0] == 'v' {
		if dot := strings.IndexByte(lower, '.'); dot > 0 {
			num, err := strconv.Atoi(lower[1:dot])
			if err != nil || num < 0 || num > 31 {
				return Register{}, false
			}
			view := lower[dot+1:]
			if open := strings.IndexByte(view, '['); open > 0 && strings.HasSuffix(view, "]") {
				letter := view[:open]
				lane, err := strconv.Atoi(view[open+1 : len(view)-1])
				if err != nil || lane < 0 || len(letter) != 1 || strings.IndexByte("bhsd", letter[0]) < 0 {
					return Register{}, false
				}
				if lane >= 16/laneBytes(letter) {
					return Register{}, false // a lane past the register
				}
				return Register{Text: lower, Class: ClassV, Num: num, Vec: letter, Lane: lane}, true
			}
			if _, ok := vectorArrangements[view]; !ok {
				return Register{}, false
			}
			return Register{Text: lower, Class: ClassV, Num: num, Vec: view, Lane: -1}, true
		}
	}
	num, err := strconv.Atoi(lower[1:])
	if err != nil || num < 0 {
		return Register{}, false
	}
	switch lower[0] {
	case 'x':
		if num <= 30 {
			return Register{Text: lower, Class: ClassX, Num: num, Lane: -1}, true
		}
	case 'w':
		if num <= 30 {
			return Register{Text: lower, Class: ClassW, Num: num, Lane: -1}, true
		}
	case 'v':
		if num <= 31 {
			return Register{Text: lower, Class: ClassV, Num: num, Lane: -1}, true
		}
	case 'b', 'h', 's', 'd', 'q':
		// Scalar views of the vector registers (FP values live here).
		if num <= 31 {
			return Register{Text: lower, Class: ClassV, Num: num, Vec: lower[:1], Lane: -1}, true
		}
	}
	return Register{}, false
}
