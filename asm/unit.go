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
	// Arch is the unit's architecture lane (docs/spec/94-assembler.md §9):
	// ArchArm64 (the default) or ArchRV64, from the unit path's
	// `.rv64.oakasm` segment or an `arch rv64` directive. Every phase —
	// parsing, the seam checker, the verifier, the encoder, the object
	// writer, and the C emitter — dispatches on it.
	Arch  string
	Items []Item
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
	// Composites: the record types that may cross this function's boundary,
	// by type name — set by the compiler from the program's record
	// declarations (never from the unit text), so the checker binds them
	// under AAPCS64's composite rules (docs/spec/94-assembler.md §9).
	Composites map[string]Composite
	// Records and ADTs: the program's monomorphic record and tagged-union
	// declarations, by name — set by the compiler so the verifier can model
	// aggregate locals of the Oak body (docs/spec/94-assembler.md §8).
	Records map[string]*ast.RecordLiteral
	ADTs    map[string]*ast.ADTType
}

// Composite is a record or tagged-union type's shape at the boundary: its
// size in bytes, whether it is a homogeneous floating-point aggregate
// (which AAPCS64 passes in v registers; v1 leaves those to the C backend),
// and its placed fields — the layout the C backend asserts — so the
// verifier can relate register chunks to the Oak body's fields. A tagged
// union's Variants map each variant to its tag; its payload fields are
// named after their variants.
type Composite struct {
	Size     int64
	HFA      bool
	Fields   []CompositeField
	Variants map[string]int64
}

// TypeApplicationName maps a type application expression (F[A][B]…, as the
// parser spells Option[u32] or Result[u32, Overflow]) to the mangled name
// of its instantiation (Option_u32, Result_u32_Overflow — the typechecker's
// Instantiation.MangledName), which is how the compiler names the
// specialized declaration. Arguments are type names or integer constants;
// a plain identifier is its own name.
func TypeApplicationName(expr ast.Expression) (string, bool) {
	switch t := expr.(type) {
	case *ast.Identifier:
		return t.Value, t.Value != ""
	case *ast.IndexExpression:
		if t.Dot || t.Index == nil {
			return "", false
		}
		if marker, isIdent := t.Index.(*ast.Identifier); isIdent && (marker.Value == "" || marker.Value == "*") {
			return "", false // a span or view, not an application
		}
		base, ok := TypeApplicationName(t.Left)
		if !ok {
			return "", false
		}
		atom, ok := typeArgumentAtom(t.Index)
		if !ok {
			return "", false
		}
		return base + "_" + atom, true
	}
	return "", false
}

func typeArgumentAtom(expr ast.Expression) (string, bool) {
	switch t := expr.(type) {
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", t.Value), true
	case *ast.Identifier:
		if t.Value == "" || t.Value == "*" {
			return "", false
		}
		return t.Value, true
	case *ast.IndexExpression:
		base, isIdent := t.Left.(*ast.Identifier)
		if !isIdent {
			return "", false
		}
		inner, ok := typeArgumentAtom(t.Index)
		if !ok {
			return "", false
		}
		return base.Value + "_" + inner, true
	}
	return "", false
}

// CompositeField is one placed member: a scalar (Scalar names its type), a
// nested composite (Type names it), or an owned array (Elem or ElemType
// the element, Length the count).
type CompositeField struct {
	Name     string
	Offset   int64
	Size     int64
	Scalar   string
	Type     string
	Elem     string
	ElemType string
	Length   int64
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
	Text  string // as written: "x0", "w5", "sp", "lr", "v3", "d1", "v0.4s", "v2.s[1]", "z0.s", "p0/m", "pn8", "za0.s", "zt0"
	Class RegClass
	Num   int // physical register number for X/W (0..30), V/Z (0..31), P (0..15), ZA tiles (0..15, -1 for the whole array); -1 for SP; 31 for zero registers
	// Vec is the vector register's view: a scalar width letter ("b", "h",
	// "s", "d", "q"), an arrangement ("8b", "16b", "4h", "8h", "2s", "4s",
	// "1d", "2d"), or "" for the whole register named as vN. For the
	// scalable classes it is the element size letter (z0.s, p0.b, za0.d),
	// "" when unsuffixed. Lane is the element index of a lane reference
	// (v0.s[1], z2.s[1], z1[0], pn8[0]), -1 when none.
	Vec  string
	Lane int
	// Qual is a predicate's qualifier: "m" (merging), "z" (zeroing), or "".
	Qual string
}

// RegisterList is the `{v0.4s, v1.4s}` operand of the structure loads, the
// `{z0.s - z3.s}` multi-vector groups, and zero's `{za0.s, za1.s}` tile list.
type RegisterList struct{ Regs []Register }

// TileSlice is a ZA operand addressed by a slice-index register: a tile
// slice (`za0h.s[w12, 0]`, `za1v.b[w13, 0:3]`), a vector group of the array
// (`za.s[w8, 0, vgx4]`), or an array vector (`za[w12, 0]`).
type TileSlice struct {
	Text   string
	Tile   int      // 0..15, or -1 for the whole array
	Dir    string   // "h", "v", or "" for an array vector
	Elem   string   // element size letter, "" for za[w12, 0]
	Index  Register // the slice index register w8-w15
	Offset int64
	Count  int    // consecutive slices named by offs1:offsN, 1 for a single slice
	Group  string // "vgx2", "vgx4", or ""
	Listed bool   // written in braces: {za0h.s[w12, 0]} of the ZA loads and stores
}

// FloatImmediate is `#0.0` and friends (fcmp, fmov).
type FloatImmediate struct{ Value float64 }

func (RegisterList) operandKind() string   { return "register list" }
func (TileSlice) operandKind() string      { return "tile slice" }
func (FloatImmediate) operandKind() string { return "float immediate" }

var vectorArrangements = map[string]int{"8b": 8, "16b": 16, "2h": 2, "4h": 4, "8h": 8, "2s": 2, "4s": 4, "1d": 1, "2d": 2, "1q": 1}
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

// Scalable reports the SVE/SME register classes (z, p, pn, za, zt0).
func (c RegClass) Scalable() bool {
	return c == ClassZ || c == ClassP || c == ClassPN || c == ClassZA || c == ClassZT
}

// vecBytesUnused keeps the earlier arrangement-width code path documented.
func vecBytesUnused(r Register) int64 {
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
	MSL   bool // `msl #n`: the shifting-ones form of the vector immediates
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
	// Extend spells how the index is read: uxtw (the checker's idiom, a
	// 32-bit element index), sxtw, lsl (a 64-bit index), or sxtx.
	Extend string
	// MulVL marks a vector-length-scaled offset: [x0, #1, mul vl] (SVE/SME).
	MulVL bool
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

// Option is a spelled operand word: a barrier option (sy, ish), a predicate
// pattern (all, vl16, pow2), a vector-length group (vlx2); Mul carries the
// `mul #n` multiplier of the element-count instructions (cntw x0, all, mul #4).
type Option struct {
	Name string
	Mul  int64
}

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
	ClassX     RegClass = iota // arm64.X — 64-bit general
	ClassW                     // arm64.W — 32-bit view
	ClassV                     // arm64.V — 128-bit vector
	ClassSP                    // arm64.SP — the stack pointer
	ClassZ                     // arm64.Z — a scalable vector register (streaming SVE); zN extends vN
	ClassP                     // arm64.P — a scalable predicate register p0-p15
	ClassPN                    // arm64.PN — a predicate-as-counter register pn0-pn15
	ClassZA                    // arm64.ZA — a ZA tile (za0.s), or the whole array (za)
	ClassZT                    // arm64.ZT — the ZT0 lookup table register
	ClassRV64X                 // rv64.X — a RISC-V 64-bit general register x0–x31 (x2 parses as ClassSP)
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
	case ClassZ:
		return "arm64.Z"
	case ClassP:
		return "arm64.P"
	case ClassPN:
		return "arm64.PN"
	case ClassZA:
		return "arm64.ZA"
	case ClassZT:
		return "arm64.ZT"
	case ClassRV64X:
		return "rv64.X"
	}
	return "?"
}

// ZeroRegister reports xzr/wzr (register number 31 in the general file)
// and RISC-V's x0 (zero).
func (r Register) ZeroRegister() bool {
	return ((r.Class == ClassX || r.Class == ClassW) && r.Num == 31) || (r.Class == ClassRV64X && r.Num == 0)
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
	unitArch := archFromPath(path)
	// parseReg reads a register in the current function's lane.
	parseReg := func(text string) (Register, bool) {
		if current != nil && current.Arch == ArchRV64 {
			return parseRV64Register(text)
		}
		return parseRegister(text)
	}
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
			current = &Function{Name: signature.Name.Value, Signature: signature, Line: lineNo, Arch: unitArch}
			continue
		}

		if line == "}" {
			if current.Arch == ArchArm64 && usesOperandStack(current) {
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
		case "arch":
			// arch rv64 — the lane, before any binding or instruction.
			if len(fields) != 2 || (fields[1] != ArchArm64 && fields[1] != ArchRV64) {
				fail(lineNo, "arch takes one of %s, %s", ArchArm64, ArchRV64)
				continue
			}
			if len(current.Items) != 0 || len(current.Bindings) != 0 || len(current.Clobbers) != 0 {
				fail(lineNo, "arch must precede every binding, clobber, and instruction")
				continue
			}
			current.Arch = fields[1]
		case "bind":
			// bind w0 = left  |  bind x0, w1 = frame
			switch {
			case len(fields) == 4 && fields[2] == "=":
				reg, ok := parseReg(fields[1])
				if !ok {
					fail(lineNo, "bind: unknown register %q", fields[1])
					continue
				}
				current.Bindings = append(current.Bindings, Binding{Register: reg, Param: fields[3], Line: lineNo})
			case len(fields) == 5 && fields[3] == "=":
				base, okBase := parseReg(fields[1])
				length, okLen := parseReg(fields[2])
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
				reg, ok := parseReg(name)
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
			if current.Arch == ArchRV64 {
				instrs, err := parseRV64Instruction(fields, lineNo)
				if err != nil {
					fail(lineNo, "%v", err)
					continue
				}
				for _, instr := range instrs {
					current.Items = append(current.Items, instr)
				}
				continue
			}
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

// archFromPath reads the lane from the unit path: `name.rv64.oakasm` is
// the RISC-V lane; `name.arm64.oakasm` and every other spelling the
// AArch64 lane.
func archFromPath(path string) string {
	for _, segment := range strings.Split(strings.ToLower(path), ".") {
		if segment == ArchRV64 {
			return ArchRV64
		}
	}
	return ArchArm64
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
		// `mul #n` multiplies the pattern word before it (cntw x0, all, mul #4).
		if strings.EqualFold(modifier, "mul") && i+1 < len(fields) && strings.HasPrefix(fields[i+1], "#") {
			mul, err := parseImmediate(fields[i+1][1:])
			if err != nil {
				return instr, err
			}
			if mul < 1 || mul > 16 {
				return instr, fmt.Errorf("mul #%d is outside 1..16", mul)
			}
			last := len(instr.Operands) - 1
			option, isOption := Option{}, false
			if last >= 0 {
				option, isOption = instr.Operands[last].(Option)
			}
			if !isOption {
				return instr, fmt.Errorf("mul #%d must follow a pattern word", mul)
			}
			option.Mul = mul
			instr.Operands[last] = option
			i++
			continue
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
		return parseRegisterList(text)
	}
	if strings.HasPrefix(text, "[") {
		return parseMemory(text)
	}
	if reg, ok := parseRegister(text); ok {
		return reg, nil
	}
	lower := strings.ToLower(text)
	if strings.HasPrefix(lower, "za") && strings.Contains(lower, "[") {
		return parseTileSlice(text)
	}
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
	if spec.tableForms && isWord(lower) {
		// SVE/SME spelled words: predicate patterns (all, vl16, pow2),
		// vector-length groups (vlx2), smstart's modes (sm, za).
		return Option{Name: lower}, nil
	}
	return nil, fmt.Errorf("unrecognized operand %q", text)
}

func isWord(s string) bool {
	if s == "" {
		return false
	}
	for _, r := range s {
		if !(r >= 'a' && r <= 'z' || r >= '0' && r <= '9') {
			return false
		}
	}
	return s[0] >= 'a' && s[0] <= 'z'
}

// parseRegisterList parses `{v0.4s, v1.4s}` (structure accesses),
// `{z0.s, z1.s}` and `{z0.s - z3.s}` (multi-vector groups), `{za0.s, za1.s}`
// and `{za}` (zero's tiles), `{zt0}`, and `{za0h.s[w12, 0]}` (one tile
// slice, the ZA loads and stores).
func parseRegisterList(text string) (Operand, error) {
	inner := strings.TrimSpace(text[1 : len(text)-1])
	if strings.Contains(inner, "[") {
		slice, err := parseTileSlice(inner)
		if err != nil {
			return nil, err
		}
		s := slice.(TileSlice)
		s.Listed = true
		return s, nil
	}
	var list RegisterList
	if inner == "" {
		return list, nil // zero { }: no tiles
	}
	for _, part := range strings.Split(inner, ",") {
		part = strings.TrimSpace(part)
		if dash := strings.IndexByte(part, '-'); dash > 0 {
			// A range `z0.s - z3.s`: consecutive registers, first to last.
			first, okFirst := parseRegister(strings.TrimSpace(part[:dash]))
			last, okLast := parseRegister(strings.TrimSpace(part[dash+1:]))
			if !okFirst || !okLast || first.Class != ClassZ || last.Class != ClassZ || first.Vec != last.Vec || first.Lane >= 0 || last.Lane >= 0 {
				return nil, fmt.Errorf("register range %q must run over z registers of one element size", part)
			}
			count := (last.Num-first.Num+32)%32 + 1
			if count < 2 || count > 4 {
				return nil, fmt.Errorf("register range %q must name two to four registers", part)
			}
			for i := 0; i < count; i++ {
				reg := first
				reg.Num = (first.Num + i) % 32
				reg.Text = fmt.Sprintf("z%d", reg.Num)
				if reg.Vec != "" {
					reg.Text += "." + reg.Vec
				}
				list.Regs = append(list.Regs, reg)
			}
			continue
		}
		reg, ok := parseRegister(part)
		if !ok {
			return nil, fmt.Errorf("register list %q holds an unknown register %q", text, part)
		}
		list.Regs = append(list.Regs, reg)
	}
	first := list.Regs[0]
	for _, reg := range list.Regs[1:] {
		if reg.Class != first.Class {
			return nil, fmt.Errorf("register list %q mixes register classes", text)
		}
	}
	switch first.Class {
	case ClassV:
		if len(list.Regs) > 4 {
			return nil, fmt.Errorf("register list %q must hold one to four registers", text)
		}
		for _, reg := range list.Regs {
			if reg.Vec == "" || reg.Lane >= 0 {
				return nil, fmt.Errorf("register list %q must hold arranged vector registers", text)
			}
			if _, arranged := vectorArrangements[reg.Vec]; !arranged {
				return nil, fmt.Errorf("register list %q must hold arranged vector registers", text)
			}
			if reg.Vec != first.Vec {
				return nil, fmt.Errorf("register list %q mixes arrangements", text)
			}
		}
	case ClassZ, ClassP:
		if len(list.Regs) > 4 {
			return nil, fmt.Errorf("register list %q must hold one to four registers", text)
		}
		for _, reg := range list.Regs {
			if reg.Lane >= 0 || reg.Vec != first.Vec || reg.Qual != "" {
				return nil, fmt.Errorf("register list %q must hold registers of one element size", text)
			}
		}
	case ClassZA:
		if len(list.Regs) > 8 {
			return nil, fmt.Errorf("tile list %q names more than eight tiles", text)
		}
		for _, reg := range list.Regs {
			if reg.Num < 0 && len(list.Regs) != 1 {
				return nil, fmt.Errorf("tile list %q names the whole array beside tiles", text)
			}
		}
	case ClassZT:
		if len(list.Regs) != 1 {
			return nil, fmt.Errorf("%q: zt0 stands alone", text)
		}
	default:
		return nil, fmt.Errorf("register list %q must hold vector, z, p, or za registers", text)
	}
	return list, nil
}

// parseTileSlice parses `za0h.s[w12, 0]`, `za1v.b[w13, 0:3]`,
// `za.s[w8, 0, vgx4]`, `za.d[w8, 7]`, and `za[w12, 0]`.
func parseTileSlice(text string) (Operand, error) {
	lower := strings.ToLower(strings.TrimSpace(text))
	open := strings.IndexByte(lower, '[')
	if open < 0 || !strings.HasSuffix(lower, "]") {
		return nil, fmt.Errorf("bad tile slice %q", text)
	}
	head, inner := lower[:open], lower[open+1:len(lower)-1]
	slice := TileSlice{Text: lower, Tile: -1, Count: 1}
	if dot := strings.IndexByte(head, '.'); dot >= 0 {
		slice.Elem = head[dot+1:]
		head = head[:dot]
		if len(slice.Elem) != 1 || strings.IndexByte("bhsdq", slice.Elem[0]) < 0 {
			return nil, fmt.Errorf("tile slice %q: element size must be b, h, s, d, or q", text)
		}
	}
	if !strings.HasPrefix(head, "za") {
		return nil, fmt.Errorf("bad tile slice %q", text)
	}
	head = head[2:]
	if head != "" {
		if strings.HasSuffix(head, "h") || strings.HasSuffix(head, "v") {
			slice.Dir = head[len(head)-1:]
			head = head[:len(head)-1]
		}
		tile, err := strconv.Atoi(head)
		if err != nil || tile < 0 || tile > 15 {
			return nil, fmt.Errorf("tile slice %q: tile number must be 0..15", text)
		}
		slice.Tile = tile
		if slice.Dir == "" {
			return nil, fmt.Errorf("tile slice %q: a tile slice names its direction (za0h or za0v)", text)
		}
		if slice.Elem == "" {
			return nil, fmt.Errorf("tile slice %q: a tile slice names its element size", text)
		}
	}
	parts := strings.Split(inner, ",")
	if len(parts) < 2 || len(parts) > 3 {
		return nil, fmt.Errorf("tile slice %q: expected [wN, offset{, vgxK}]", text)
	}
	index, ok := parseRegister(strings.TrimSpace(parts[0]))
	if !ok || index.Class != ClassW || index.Num < 8 || index.Num > 15 {
		return nil, fmt.Errorf("tile slice %q: the slice index register is one of w8-w15", text)
	}
	slice.Index = index
	offs := strings.TrimSpace(parts[1])
	if colon := strings.IndexByte(offs, ':'); colon >= 0 {
		first, err1 := strconv.Atoi(offs[:colon])
		last, err2 := strconv.Atoi(offs[colon+1:])
		if err1 != nil || err2 != nil || first < 0 || last < first || last-first+1 > 4 {
			return nil, fmt.Errorf("tile slice %q: bad offset range %q", text, offs)
		}
		slice.Offset = int64(first)
		slice.Count = last - first + 1
	} else {
		value, err := strconv.Atoi(offs)
		if err != nil || value < 0 || value > 15 {
			return nil, fmt.Errorf("tile slice %q: offset must be 0..15", text)
		}
		slice.Offset = int64(value)
	}
	if len(parts) == 3 {
		group := strings.TrimSpace(parts[2])
		if group != "vgx2" && group != "vgx4" {
			return nil, fmt.Errorf("tile slice %q: vector group must be vgx2 or vgx4", text)
		}
		if slice.Tile >= 0 {
			return nil, fmt.Errorf("tile slice %q: a vector group addresses the array (za.s[...]), not a tile", text)
		}
		slice.Group = group
	}
	return slice, nil
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
		var u uint64
		u, err = strconv.ParseUint(text[2:], 16, 64) // full 64-bit patterns (0xffff0000ffff0000)
		value = int64(u)
	} else {
		var u uint64
		u, err = strconv.ParseUint(text, 10, 64) // up to 2^63 in magnitude
		value = int64(u)
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
	if len(parts) == 2 && !strings.HasPrefix(strings.TrimSpace(parts[1]), "#") {
		// [base, xI]: a 64-bit register offset (LSL #0).
		index, ok := parseRegister(strings.TrimSpace(parts[1]))
		if !ok || index.Class != ClassX {
			return nil, fmt.Errorf("memory offset must be an immediate or an x register, got %q", strings.TrimSpace(parts[1]))
		}
		if pre {
			return nil, fmt.Errorf("register-offset addressing has no pre-index form")
		}
		mem.Index = &index
		mem.Extend = "lsl"
		return mem, nil
	}
	if len(parts) == 2 {
		offsetText := strings.TrimSpace(parts[1])
		offset, err := parseImmediate(offsetText[1:])
		if err != nil {
			return nil, err
		}
		mem.Offset = offset
	} else if len(parts) == 3 && strings.HasPrefix(strings.TrimSpace(parts[1]), "#") {
		// [base, #imm, mul vl]: a vector-length-scaled offset (SVE/SME).
		offset, err := parseImmediate(strings.TrimSpace(parts[1])[1:])
		if err != nil {
			return nil, err
		}
		if strings.Join(strings.Fields(strings.ToLower(parts[2])), " ") != "mul vl" {
			return nil, fmt.Errorf("memory operand %q: an immediate offset is followed only by `mul vl`", text)
		}
		if pre {
			return nil, fmt.Errorf("vector-length offsets have no pre-index form")
		}
		mem.Offset = offset
		mem.MulVL = true
	} else if len(parts) == 3 {
		// [base, wI, uxtw #s] (the checker's idiom), [base, wI, sxtw #s],
		// [base, xI, lsl #s], [base, xI, sxtx #s].
		index, ok := parseRegister(strings.TrimSpace(parts[1]))
		if !ok || index.Class != ClassW && index.Class != ClassX {
			return nil, fmt.Errorf("memory index must be a general register, got %q", strings.TrimSpace(parts[1]))
		}
		extend := strings.Fields(strings.ToLower(strings.TrimSpace(parts[2])))
		if len(extend) == 0 || len(extend) > 2 {
			return nil, fmt.Errorf("memory index extension must be `uxtw #s`, got %q", strings.TrimSpace(parts[2]))
		}
		switch {
		case index.Class == ClassW && (extend[0] == "uxtw" || extend[0] == "sxtw"):
		case index.Class == ClassX && (extend[0] == "lsl" || extend[0] == "sxtx"):
		default:
			return nil, fmt.Errorf("memory index %s takes uxtw/sxtw (w) or lsl/sxtx (x), got %q", index.Text, extend[0])
		}
		mem.Extend = extend[0]
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
	// The scalable file: z, p, pn, za, zt0.
	if lower[0] == 'z' || lower[0] == 'p' {
		return parseScalableRegister(lower)
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
				// A lane (`v0.s[1]`) or a lane group (`v0.4b[1]`, `v0.2h[1]` —
				// the dot-product by-element forms index 32-bit groups).
				letter := view[:open]
				group := 1
				if len(letter) == 2 && (letter == "4b" || letter == "2h") {
					group = int(letter[0] - '0')
					letter = letter[1:]
				}
				lane, err := strconv.Atoi(view[open+1 : len(view)-1])
				if err != nil || lane < 0 || len(letter) != 1 || strings.IndexByte("bhsd", letter[0]) < 0 {
					return Register{}, false
				}
				if lane >= 16/(group*laneBytes(letter)) {
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

// parseScalableRegister recognizes the SVE/SME register file
// (docs/spec/94-assembler.md §3): z0-z31 with an element size (`z0.s`),
// bare (`z0`), or indexed (`z2.s[1]`, `z1[0]`); predicates p0-p15 with an
// element size or a qualifier (`p0.b`, `p0/m`, `p0/z`); predicate-as-counter
// registers pn0-pn15 (`pn8`, `pn8.s`, `pn8/z`, `pn8[0]`); ZA tiles
// (`za0.s`, `za5.d`) and the whole array (`za`); and `zt0`.
func parseScalableRegister(lower string) (Register, bool) {
	reg := Register{Text: lower, Lane: -1}
	rest := ""
	switch {
	case lower == "za":
		return Register{Text: lower, Class: ClassZA, Num: -1, Lane: -1}, true
	case lower == "zt0":
		return Register{Text: lower, Class: ClassZT, Num: 0, Lane: -1}, true
	case strings.HasPrefix(lower, "za"):
		reg.Class = ClassZA
		rest = lower[2:]
	case strings.HasPrefix(lower, "pn"):
		reg.Class = ClassPN
		rest = lower[2:]
	case lower[0] == 'z':
		reg.Class = ClassZ
		rest = lower[1:]
	default:
		reg.Class = ClassP
		rest = lower[1:]
	}
	// The number, then any of `.e`, `/q`, `[i]`.
	digits := 0
	for digits < len(rest) && rest[digits] >= '0' && rest[digits] <= '9' {
		digits++
	}
	if digits == 0 {
		return Register{}, false
	}
	num, err := strconv.Atoi(rest[:digits])
	if err != nil {
		return Register{}, false
	}
	limit := 31
	if reg.Class != ClassZ {
		limit = 15
	}
	if num > limit {
		return Register{}, false
	}
	reg.Num = num
	rest = rest[digits:]
	if strings.HasPrefix(rest, ".") {
		if len(rest) < 2 || strings.IndexByte("bhsdq", rest[1]) < 0 {
			return Register{}, false
		}
		reg.Vec = rest[1:2]
		rest = rest[2:]
	}
	if strings.HasPrefix(rest, "/") {
		if reg.Class != ClassP && reg.Class != ClassPN || len(rest) != 2 || rest[1] != 'm' && rest[1] != 'z' {
			return Register{}, false
		}
		reg.Qual = rest[1:2]
		rest = ""
	}
	if strings.HasPrefix(rest, "[") && strings.HasSuffix(rest, "]") {
		if reg.Class != ClassZ && reg.Class != ClassPN {
			return Register{}, false
		}
		lane, err := strconv.Atoi(rest[1 : len(rest)-1])
		if err != nil || lane < 0 || lane > 15 {
			return Register{}, false
		}
		reg.Lane = lane
		rest = ""
	}
	if rest != "" {
		return Register{}, false
	}
	if reg.Class == ClassZA && reg.Vec == "" {
		return Register{}, false // a tile names its element size (za0.s); the array is `za`
	}
	return reg, true
}
