package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// emitBytePack recognizes a complete little-endian byte pack over one u8
// view and a side-effect-free u32 offset. One range check subsumes the original
// per-byte checks. Byte accesses retain portable alignment and alias semantics;
// the native compiler can combine them into an unaligned word load.
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
	for lane, term := range terms {
		shift, ok := term.(*ast.InfixExpression)
		if !ok || shift.Operator != "<<" || !bytePackConstant(shift.Right, width, int64(lane*8)) {
			return false
		}
		cast, ok := shift.Left.(*ast.InvocationExpression)
		if !ok || len(cast.Arguments) != 1 || !bytePackName(cast.Function, width) {
			return false
		}
		var base, index ast.Expression
		switch access := cast.Arguments[0].(type) {
		case *ast.IndexExpression:
			if access.Dot {
				return false
			}
			base, index = access.Left, access.Index
		case *ast.InvocationExpression:
			if !bytePackName(access.Function, "core_index") || len(access.Arguments) != 2 {
				return false
			}
			base, index = access.Arguments[0], access.Arguments[1]
		default:
			return false
		}
		v, ok := base.(*ast.Identifier)
		if !ok {
			return false
		}
		info := cg.localContainerOf(v)
		if info.kind != containerView || info.element != "u8" {
			return false
		}
		add, ok := index.(*ast.InfixExpression)
		if !ok || add.Operator != "+" || !bytePackConstant(add.Right, "u32", int64(lane)) {
			return false
		}
		o, ok := add.Left.(*ast.Identifier)
		if !ok || (lane != 0 && (v.Value != view.Value || o.Value != offset.Value)) {
			return false
		}
		view, offset = v, o
	}
	name := "oak_byte_pack_le_" + width
	var body strings.Builder
	fmt.Fprintf(&body, "static inline %s %s(oak_view_u8 src, u32 off) {\n", width, name)
	fmt.Fprintf(&body, "  if ((u64)off + %du > (u64)src.len) { __builtin_trap(); }\n", len(terms))
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
	cg.emitExpressionFragment(offset, tc)
	cg.output.WriteString(" )")
	return true
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
