package asm

import (
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// ReturnSlotLocal selects a record or array local the body builds in the
// caller's result area: the body's tail is its bare name, declared once
// at the body's top level with the result type, and its address is never
// taken. Record literals are excluded because their initializer fills
// frame storage. The native backend builds such a local in place where
// it can (docs/spec/94-assembler.md §9 "Copies at the boundary") and
// records the one it placed as Function.ResultSlot, from which the
// verifier reads the result area's large array fields as the local's
// span memories (resultSpanFields) on both sides.
func ReturnSlotLocal(fn *ast.FunctionStatement) string {
	if fn == nil {
		return ""
	}
	block, isBlock := fn.Body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil || len(block.Block.Statements) < 2 || fn.ReturnType == nil {
		return ""
	}
	stmts := block.Block.Statements
	tail, isExpr := stmts[len(stmts)-1].(*ast.ExpressionStatement)
	if !isExpr || tail.Discard {
		return ""
	}
	ident, isIdent := tail.Expression.(*ast.Identifier)
	if !isIdent {
		return ""
	}
	name := ident.Value
	for _, p := range fn.Parameters {
		if p.Name != nil && p.Name.Value == name {
			return ""
		}
	}
	topLevel := false
	for _, stmt := range stmts[:len(stmts)-1] {
		decl, isDecl := stmt.(*ast.VariableDeclaration)
		if !isDecl || decl.Name == nil || decl.Name.Value != name {
			continue
		}
		if decl.Type == nil || decl.Type.String() != fn.ReturnType.String() {
			return ""
		}
		if _, isLiteral := decl.Value.(*ast.RecordLiteral); isLiteral {
			return ""
		}
		topLevel = true
	}
	if !topLevel {
		return ""
	}
	declarations, ok := 0, true
	walkASTNodes(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.VariableDeclaration:
			if e.Name != nil && e.Name.Value == name {
				declarations++
			}
		case *ast.PrefixExpression:
			if e.Operator == "&" {
				if root, has := accessPathRoot(e.Right); has && root == name {
					ok = false
				}
			}
		}
	})
	if declarations != 1 || !ok {
		return ""
	}
	return name
}

// accessPathRoot is the identifier an access path starts at.
func accessPathRoot(expr ast.Expression) (string, bool) {
	for {
		switch e := expr.(type) {
		case *ast.Identifier:
			return e.Value, true
		case *ast.IndexExpression:
			expr = e.Left
		default:
			return "", false
		}
	}
}

// resultSpanField is an array field of the result record the verifier
// reads as a span memory of the return-slot local on both sides: at
// least spanArrayFieldElements integer elements, named `<local>.<field>`.
type resultSpanField struct {
	name   string // the span memory: `out.at`
	field  string
	offset int64 // the field's byte offset in the record
	size   int64
	elem   int64 // the element size in bytes
	signed bool
}

// SpanArrayFieldElements is spanArrayFieldElements for the backend: the
// element count from which it names a record local's array field as a
// frame object of its own (`local.field`), which the verifier reads as a
// span memory when the local is declared value-less.
const SpanArrayFieldElements = spanArrayFieldElements

// localValueless reports a local declared without an initializer (`out:
// Bits`): zero at entry, the backend's fill. A local built from an
// initializer (`next: State = state`) keeps the leaf model, under which
// BLAKE3's update proves; its copy of the parameter into the span
// coupled past the search's budget.
func localValueless(sig *ast.FunctionStatement, name string) bool {
	if name == "" || sig == nil {
		return false
	}
	valueless := false
	walkASTNodes(sig.Body, func(n ast.Node) {
		if decl, isDecl := n.(*ast.VariableDeclaration); isDecl && decl.Name != nil && decl.Name.Value == name && decl.Value == nil {
			valueless = true
		}
	})
	return valueless
}

// returnSlotValueless is localValueless for the return slot.
func returnSlotValueless(sig *ast.FunctionStatement, slot string) bool {
	return localValueless(sig, slot)
}

// frameSpanLocal is the local a frame object named `local.field` belongs
// to, "" for an array local's own object.
func frameSpanLocal(name string) string {
	if dot := strings.IndexByte(name, '.'); dot > 0 {
		return name[:dot]
	}
	return ""
}

// resultSpanFields lists the result record's span fields for a body whose
// return-slot local is slot, declared value-less (none otherwise).
func resultSpanFields(fn *Function, sig *ast.FunctionStatement, slot string) []resultSpanField {
	if slot == "" || sig == nil || sig.ReturnType == nil || !returnSlotValueless(sig, slot) {
		return nil
	}
	comp, isComposite := fn.Composites[typeText(sig.ReturnType)]
	if !isComposite {
		return nil
	}
	var out []resultSpanField
	for _, field := range comp.Fields {
		if field.Length < spanArrayFieldElements || field.Elem == "" || field.Elem == "Bool" || strings.HasPrefix(field.Elem, "f") {
			continue
		}
		width, signed, ok := contractBits(&ast.Identifier{Value: field.Elem})
		if !ok || width < 8 || int64(width)*field.Length != field.Size*8 {
			continue
		}
		out = append(out, resultSpanField{name: slot + "." + field.Name, field: field.Name, offset: field.Offset, size: field.Size, elem: int64(width / 8), signed: signed})
	}
	return out
}
