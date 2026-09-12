package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// emitBytePack recognizes a complete little-endian byte pack over one u8
// view and a side-effect-free offset, `src[o + K] .. src[o + K + L - 1]`
// for a literal base `K`. One range check subsumes the original per-byte
// checks, and when the checker proved every byte in range
// (typechecker/extents.go) the `_proven` twin carries none. Byte accesses
// retain portable alignment and alias semantics; the native compiler can
// combine them into an unaligned word load.
func (cg *CodeGenerator) emitBytePack(expr *ast.InfixExpression, tc *typechecker.TypeChecker) bool {
	if expr.Operator != "|" {
		return false
	}
	var terms []ast.Expression
	var collect func(ast.Expression)
	collect = func(e ast.Expression) {
		if op, ok := e.(*ast.InfixExpression); ok && op.Operator == "|" {
			collect(op.Left)
			collect(op.Right)
		} else {
			terms = append(terms, e)
		}
	}
	collect(expr)
	if len(terms) != 4 && len(terms) != 8 {
		return false
	}
	width := fmt.Sprintf("u%d", len(terms)*8)
	var view, offset *ast.Identifier
	base := int64(0)
	proven := tc != nil
	for lane, term := range terms {
		shift, ok := term.(*ast.InfixExpression)
		if !ok || shift.Operator != "<<" || !bytePackConstant(shift.Right, width, int64(lane*8)) {
			return false
		}
		cast, ok := shift.Left.(*ast.InvocationExpression)
		if !ok || len(cast.Arguments) != 1 || !bytePackName(cast.Function, width) {
			return false
		}
		var container, index ast.Expression
		var token token.Token
		switch access := cast.Arguments[0].(type) {
		case *ast.IndexExpression:
			if access.Dot {
				return false
			}
			container, index, token = access.Left, access.Index, access.Token
		case *ast.InvocationExpression:
			if !bytePackName(access.Function, "core_index") || len(access.Arguments) != 2 {
				return false
			}
			container, index, token = access.Arguments[0], access.Arguments[1], access.Token
		default:
			return false
		}
		v, ok := container.(*ast.Identifier)
		if !ok {
			return false
		}
		info := cg.localContainerOf(v)
		if info.kind != containerView || info.element != "u8" {
			return false
		}
		add, ok := index.(*ast.InfixExpression)
		if !ok || add.Operator != "+" {
			return false
		}
		if lane == 0 {
			k, isConst := bytePackLiteral(add.Right, "u32")
			if !isConst || k < 0 {
				return false
			}
			base = k
		} else if !bytePackConstant(add.Right, "u32", base+int64(lane)) {
			return false
		}
		if proven && !tc.IndexProven(token) {
			proven = false
		}
		o, ok := add.Left.(*ast.Identifier)
		if !ok || (lane != 0 && (v.Value != view.Value || o.Value != offset.Value)) {
			return false
		}
		view, offset = v, o
	}
	name := "oak_byte_pack_le_" + width
	if proven {
		name += "_proven"
	}
	var body strings.Builder
	fmt.Fprintf(&body, "static inline %s %s(oak_view_u8 src, u64 off) {\n", width, name)
	if proven {
		body.WriteString("  /* every byte proven in range by the checker (Oak.Extents): no check */\n")
	} else {
		fmt.Fprintf(&body, "  if (off > (u64)src.len || %du > (u64)src.len - off) { __builtin_trap(); }\n", len(terms))
	}
	body.WriteString("  const u8 *p = src.base + off;\n  return ")
	for lane := range terms {
		if lane != 0 {
			body.WriteString(" | ")
		}
		fmt.Fprintf(&body, "((%s)p[%d] << %d)", width, lane, lane*8)
	}
	body.WriteString(";\n}\n\n")
	cg.sliceHelpers[name] = body.String()
	cg.output.WriteString(name + "( ")
	cg.emitExpressionFragment(view, tc)
	cg.output.WriteString(", ")
	if base != 0 {
		cg.output.WriteString("(u64)( ")
		cg.emitExpressionFragment(offset, tc)
		cg.output.WriteString(fmt.Sprintf(" ) + %du", base))
	} else {
		cg.emitExpressionFragment(offset, tc)
	}
	cg.output.WriteString(" )")
	return true
}

// bytePackLiteral reads a width-typed literal constructor `u32(K)`.
func bytePackLiteral(expr ast.Expression, width string) (int64, bool) {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(call.Arguments) != 1 || !bytePackName(call.Function, width) {
		return 0, false
	}
	literal, ok := call.Arguments[0].(*ast.IntegerLiteral)
	if !ok {
		return 0, false
	}
	return literal.Value, true
}

func bytePackName(expr ast.Expression, name string) bool {
	id, ok := expr.(*ast.Identifier)
	return ok && id.Value == name
}

func bytePackConstant(expr ast.Expression, width string, value int64) bool {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(call.Arguments) != 1 || !bytePackName(call.Function, width) {
		return false
	}
	literal, ok := call.Arguments[0].(*ast.IntegerLiteral)
	return ok && literal.Value == value
}
