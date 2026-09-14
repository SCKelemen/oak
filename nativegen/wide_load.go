package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// The little-endian word idiom (docs/spec/94-assembler.md §9): an Oak body
// assembling a word from a span's consecutive bytes,
//
//	u64(v[i]) | (u64(v[i + u32(1)]) << u64(8)) | … | (u64(v[i + u32(7)]) << u64(56))
//
// is what the hash and codec kernels write to read a word from a byte
// view (stdlib/hash.oak crc32c_word_at). Lowered term by term it is N
// guarded `ldrb`s shifted and or-ed together; the machine reads the same
// word with one `ldr` at the first byte's address, so the lowering emits
// that: one guard proving the N bytes lie inside the span (the vector
// lowering's slack guard, `len >= N` and `i <= len - N`, which the seam
// checker admits for an access N elements wide — asm/check.go
// indexedSpanAccess) and one load. The verifier reads the wide load as the
// concatenation of the N elements (asm/verify.go wideElementIn), so the
// body stays proven equal to its Oak text. Measured on CRC-32C
// (benchmarks/native/README.md): fifty-six guarded byte loads per chunk
// became seven guarded word loads.

// wideLoadTerm is one term of the idiom: the element index expression and
// the bit position the byte lands at.
type wideLoadTerm struct {
	index ast.Expression
	shift int64
	tok   token.Token // the element access, for the checker's proof
}

// wideLoad recognizes the idiom in an `|` expression of unsigned type typ
// and lowers it to one load. It reports whether it handled the expression;
// when it did not, nothing was emitted and the caller lowers term by term.
func (g *generator) wideLoad(e *ast.InfixExpression, typ scalar) (int, bool, error) {
	if typ.signed || typ.isFloat || typ.isVec || typ.isBool || typ.bits < 16 {
		return 0, false, nil
	}
	// Flatten the left-associated or chain.
	var operands []ast.Expression
	for cur := ast.Expression(e); ; {
		infix, isInfix := cur.(*ast.InfixExpression)
		if !isInfix || infix.Operator != "|" {
			operands = append(operands, cur)
			break
		}
		operands = append(operands, infix.Right)
		cur = infix.Left
	}
	// Every operand: T(v[index]) or T(v[index]) << K, over one span v.
	spanName := ""
	terms := make([]wideLoadTerm, 0, len(operands))
	for _, operand := range operands {
		shift := int64(0)
		if infix, isInfix := operand.(*ast.InfixExpression); isInfix && infix.Operator == "<<" {
			k, isConst := constantValue(infix.Right)
			if !isConst || k <= 0 || k%8 != 0 || k >= int64(typ.bits) {
				return 0, false, nil
			}
			shift, operand = k, infix.Left
		}
		call, isCall := operand.(*ast.InvocationExpression)
		if !isCall || len(call.Arguments) != 1 {
			return 0, false, nil
		}
		if conv, isIdent := call.Function.(*ast.Identifier); !isIdent || conv.Value != typ.name {
			return 0, false, nil
		}
		index, isIndex := call.Arguments[0].(*ast.IndexExpression)
		if !isIndex || index.Dot {
			return 0, false, nil
		}
		ident, isIdent := index.Left.(*ast.Identifier)
		if !isIdent || (spanName != "" && ident.Value != spanName) {
			return 0, false, nil
		}
		spanName = ident.Value
		terms = append(terms, wideLoadTerm{index: index.Index, shift: shift, tok: index.Token})
	}
	sp, isSpan := g.spans[spanName]
	if !isSpan || sp.atomic || sp.elemLayout != nil || sp.array != nil || sp.frameLen > 0 {
		return 0, false, nil
	}
	// Bytes only in this increment: the load's scale is the element's, and
	// the concatenation the verifier builds is byte-granular.
	if sp.elem.bits != 8 || sp.elem.signed || sp.elem.isFloat || sp.elem.isBool {
		return 0, false, nil
	}
	count := int64(typ.bits / 8)
	if int64(len(terms)) != count {
		return 0, false, nil
	}
	// The byte at bit 8k is element base + k, each position exactly once.
	var base ast.Expression
	for _, t := range terms {
		if t.shift == 0 {
			if base != nil {
				return 0, false, nil
			}
			base = t.index
		}
	}
	if base == nil {
		return 0, false, nil
	}
	baseConst, baseIsConst := constantValue(base)
	seen := make([]bool, count)
	for _, t := range terms {
		k := t.shift / 8
		if seen[k] {
			return 0, false, nil
		}
		seen[k] = true
		if k == 0 {
			continue
		}
		if baseIsConst {
			c, isConst := constantValue(t.index)
			if !isConst || c != baseConst+k {
				return 0, false, nil
			}
			continue
		}
		sum, isSum := t.index.(*ast.InfixExpression)
		if !isSum || sum.Operator != "+" {
			return 0, false, nil
		}
		offset, isConst := constantValue(sum.Right)
		if !isConst || offset != k || sum.Left.String() != base.String() {
			return 0, false, nil
		}
	}
	if baseIsConst && (baseConst < 0 || baseConst+count > 1<<32) {
		return 0, false, nil
	}
	// Recognized. A constant base whose every byte the typechecker proved
	// in range (the inlined `word_at(chunk, u32(48))` under the caller's
	// `len(chunk) >= u32(56)`) is one load at the immediate offset, no
	// guard: the seam checker bounds it by the span's proven minimum
	// length (asm/check.go, "touches span bytes … but the guard proves only
	// N elements"). The offset must scale for the load's immediate form.
	if baseIsConst && g.elide && g.tc != nil && baseConst%count == 0 && baseConst <= 4095*count {
		proven := true
		for _, t := range terms {
			if !g.tc.IndexProven(t.tok) {
				proven = false
				break
			}
		}
		if proven {
			out, err := g.alloc(typ)
			if err != nil {
				return 0, false, err
			}
			load := "ldr"
			if typ.bits == 16 {
				load = "ldrh"
			}
			g.emit(load, reg(out, typ), asm.Memory{Base: xr(sp.baseReg), Offset: baseConst})
			g.elided += int(count)
			return out, true, nil
		}
	}
	// The index in a scratch register, the slack guard, the load.
	r, err := g.indexValue(base)
	if err != nil {
		return 0, false, err
	}
	if g.provenLanes(spanName, base) < count {
		limit, err := g.alloc(scalars["u32"])
		if err != nil {
			return 0, false, err
		}
		g.usedTrap = true
		g.emit("cmp", wr(sp.lenReg), imm(count))
		g.branch("lo", g.trap)
		g.emit("sub", wr(limit), wr(sp.lenReg), imm(count))
		g.emit("cmp", wr(r), wr(limit))
		g.branch("hi", g.trap)
		g.release(limit)
	}
	out, err := g.alloc(typ)
	if err != nil {
		return 0, false, err
	}
	index := wr(r)
	address := asm.Memory{Base: xr(sp.baseReg), Index: &index, Shift: 0, Extend: "uxtw"}
	load := "ldr"
	if typ.bits == 16 {
		load = "ldrh"
	}
	g.emit(load, reg(out, typ), address)
	g.release(r)
	return out, true, nil
}
