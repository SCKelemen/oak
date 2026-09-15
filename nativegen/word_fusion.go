package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
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
	// proven: the typechecker proved every byte access in range, so under
	// Lane.ElideProven the load needs no guard of its own — the source's
	// own guard (`len(chunk) >= at + 8`) is the slack fact the checker
	// admits the wide access under (sumFacts, docs/spec/94-assembler.md §7).
	proven bool
}

// wordTerm is one term of the or tree: the span, the index base, the
// byte offset from it, and the shift in bits.
type wordTerm struct {
	span   string
	base   ast.Expression
	offset int64
	shift  int64
	tok    *token.Token // the element access, for the typechecker's proof
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
	proven := g.elide && g.tc != nil
	for _, t := range terms {
		if t.tok == nil || !g.tc.IndexProven(*t.tok) {
			proven = false
		}
	}
	return wordAssembly{span: first.span, index: first.base, bytes: width, proven: proven}, true
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
	tok := access.Token
	return wordTerm{span: spanName.Value, base: base, offset: offset, shift: shift, tok: &tok}, true
}

// fusedWordLoad emits the recognized word assembly as one wide load under
// the slack guard and returns the register holding the word.
func (g *generator) fusedWordLoad(w wordAssembly, typ scalar) (int, error) {
	sp := g.spans[w.span]
	if k, isConst := constantValue(w.index); isConst && w.proven && k >= 0 && k%w.bytes == 0 && k <= 4095*w.bytes {
		// A constant base whose every byte is proven (an inlined
		// `word_at(chunk, u32(48))` under the caller's `len(chunk) >= 56`,
		// the literal substituted by compiler/inline.go): one load at the
		// immediate offset, which the checker bounds by the span's proven
		// minimum length; a register index would need a slack fact no
		// guard here produced.
		out, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		address := asm.Memory{Base: xr(sp.baseReg), Offset: k}
		switch w.bytes {
		case 8:
			g.emit("ldr", xr(out), address)
		case 4:
			g.emit("ldr", wr(out), address)
		default:
			g.emit("ldrh", wr(out), address)
		}
		g.elided++
		g.fusedWords++
		return out, nil
	}
	idx, err := g.indexValue(w.index)
	if err != nil {
		return 0, err
	}
	if w.proven {
		// Every byte proven in range: the source's guard is the fact.
		g.elided++
	} else {
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
	}
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

// rvFusedWordLoad is fusedWordLoad on the rv64 lane: the slack guard in
// the lane's shape (`li k, K; bltu norm, k, trap; sub t, norm, k; bltu t,
// idx, trap`, Oak.RiscV.slack_guard), then the element address and one
// `ld`/`lwu`/`lhu` at it — the checker admits the wider access through a
// region the guard marked K lanes deep.
func (g *rvGenerator) rvFusedWordLoad(w wordAssembly, typ scalar) (int, error) {
	sp := g.spans[w.span]
	idxType, err := g.typeOf(w.index, nil)
	if err != nil {
		return 0, err
	}
	if idxType.isBool || idxType.isFloat || idxType.isVec || (idxType.signed && idxType.bits != 32) {
		return 0, unsupported("an element index of type %s (indices are unsigned or i32)", idxType.name)
	}
	r, err := g.expr(w.index, &idxType)
	if err != nil {
		return 0, err
	}
	R := rvReg(r)
	if idxType.bits < 64 && !idxType.signed {
		g.emit("slli", R, R, imm(32))
		g.emit("srli", R, R, imm(32))
	}
	k, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	t, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	g.usedTrap = true
	g.emit("li", rvReg(k), imm(w.bytes))
	g.emit("bltu", rvReg(sp.norm), rvReg(k), asm.Symbol{Name: g.trap})
	g.emit("sub", rvReg(t), rvReg(sp.norm), rvReg(k))
	g.emit("bltu", rvReg(t), R, asm.Symbol{Name: g.trap})
	g.release(t)
	g.release(k)
	g.emit("add", R, rvReg(sp.baseReg), R)
	load := "ld"
	switch w.bytes {
	case 4:
		load = "lwu"
	case 2:
		load = "lhu"
	}
	g.emit(load, R, asm.Memory{Base: R, Offset: 0, Mode: asm.MemOffset})
	g.fusedWords++
	return r, nil
}
