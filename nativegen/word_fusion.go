package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

// Word fusion (docs/spec/94-assembler.md §9, wide loads): the little-endian
// word assembly `u64(v[i]) | u64(v[i+1]) << 8 | … | u64(v[i+7]) << 56` over
// a byte span — the shape `bytes_read_u64_le` and the hash kernels spell —
// is one wide load. The lowering recognizes the or tree whose terms are
// the span's bytes at consecutive offsets from one index, each shifted to
// its position, and emits the slack guard `i + n <= len` (the vector idiom
// the checker admits a wide access under) and one `ldr` of the width at
// `[base, wI, uxtw]`. The verifier models a load wider than the element as
// the same or of shifted bytes (Oak.Assembler.wide_load_assembles), so the
// fused load proves equal to the eight reads.

// wordAssembly is a recognized word assembly: the byte span, the index
// expression of byte 0, and the word width in bytes.
type wordAssembly struct {
	span  string
	index ast.Expression
	bytes int64
}

// wordTerm is one term of the or tree: the span, the index base, the
// byte offset from it, and the shift in bits.
type wordTerm struct {
	span   string
	base   ast.Expression
	offset int64
	shift  int64
}

// recognizeWordAssembly reads an `|` expression as a word assembly at the
// result type's width, or reports false.
func (g *generator) recognizeWordAssembly(e *ast.InfixExpression, typ scalar) (wordAssembly, bool) {
	if e.Operator != "|" || typ.isFloat || typ.isVec || typ.isBool || typ.signed {
		return wordAssembly{}, false
	}
	width := int64(typ.bits / 8)
	if width != 2 && width != 4 && width != 8 {
		return wordAssembly{}, false
	}
	var terms []wordTerm
	var flatten func(expr ast.Expression) bool
	flatten = func(expr ast.Expression) bool {
		if or, isOr := expr.(*ast.InfixExpression); isOr && or.Operator == "|" {
			return flatten(or.Left) && flatten(or.Right)
		}
		term, ok := g.wordTermOf(expr, typ)
		if !ok {
			return false
		}
		terms = append(terms, term)
		return true
	}
	if !flatten(e) || int64(len(terms)) != width {
		return wordAssembly{}, false
	}
	first := terms[0]
	seen := make([]bool, width)
	for _, t := range terms {
		if t.span != first.span || t.base.String() != first.base.String() {
			return wordAssembly{}, false
		}
		if t.offset < 0 || t.offset >= width || seen[t.offset] || t.shift != 8*t.offset {
			return wordAssembly{}, false
		}
		seen[t.offset] = true
	}
	if g.callsProgramFunction(first.base) {
		return wordAssembly{}, false
	}
	return wordAssembly{span: first.span, index: first.base, bytes: width}, true
}

// wordTermOf reads one term: `conv(v[base])`, `conv(v[base + k])`, or
// either shifted left by a literal (possibly through a conversion of a
// literal), over a byte span v of the function.
func (g *generator) wordTermOf(expr ast.Expression, typ scalar) (wordTerm, bool) {
	shift := int64(0)
	if sh, isShift := expr.(*ast.InfixExpression); isShift && sh.Operator == "<<" {
		k, isConst := g.constantOperand(sh.Right, typ)
		if !isConst {
			return wordTerm{}, false
		}
		shift = int64(k)
		expr = sh.Left
	}
	// The conversion to the word's type.
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return wordTerm{}, false
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || fn.Value != typ.name {
		return wordTerm{}, false
	}
	access, isIndex := call.Arguments[0].(*ast.IndexExpression)
	if !isIndex || access.Dot {
		return wordTerm{}, false
	}
	spanName, isSpanIdent := access.Left.(*ast.Identifier)
	if !isSpanIdent {
		return wordTerm{}, false
	}
	sp, isSpan := g.spans[spanName.Value]
	if !isSpan || sp.elemLayout != nil || sp.elem.bits != 8 || sp.elem.signed || sp.atomic {
		return wordTerm{}, false
	}
	base, offset := access.Index, int64(0)
	if sum, isSum := access.Index.(*ast.InfixExpression); isSum && sum.Operator == "+" {
		if k, isConst := constantValue(sum.Right); isConst && k >= 0 {
			base, offset = sum.Left, k
		}
	}
	return wordTerm{span: spanName.Value, base: base, offset: offset, shift: shift}, true
}

// fusedWordLoad emits the recognized word assembly as one wide load under
// the slack guard and returns the register holding the word.
func (g *generator) fusedWordLoad(w wordAssembly, typ scalar) (int, error) {
	sp := g.spans[w.span]
	idx, err := g.indexValue(w.index)
	if err != nil {
		return 0, err
	}
	limit, err := g.alloc(scalars["u32"])
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	g.emit("cmp", wr(sp.lenReg), imm(w.bytes))
	g.branch("lo", g.trap)
	g.emit("sub", wr(limit), wr(sp.lenReg), imm(w.bytes))
	g.emit("cmp", wr(idx), wr(limit))
	g.branch("hi", g.trap)
	g.release(limit)
	out, err := g.alloc(typ)
	if err != nil {
		return 0, err
	}
	index := wr(idx)
	address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: 0, Extend: "uxtw"}
	switch w.bytes {
	case 8:
		g.emit("ldr", xr(out), address)
	case 4:
		g.emit("ldr", wr(out), address)
	default:
		g.emit("ldrh", wr(out), address)
	}
	g.release(idx)
	g.fusedWords++
	return out, nil
}
