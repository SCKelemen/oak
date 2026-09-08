package borrowchecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Aggregate storage needs field-sensitive provenance and destination lifetimes.
// Until those are represented, reject writes that would hide borrowed access.
// Ordinary view/span bindings continue through the existing borrow machinery.
func (bc *BorrowChecker) checkAggregateStorage(value ast.Expression, env *typechecker.TypeEnvironment, element bool) {
	typ := env.CheckedExpressionType(value)
	bc.checkAggregateType(value, typ, env, element)
}

func (bc *BorrowChecker) checkAggregateType(origin ast.Node, typ typechecker.Type, env *typechecker.TypeEnvironment, element bool) {
	if !element {
		if _, ok := typ.(*typechecker.StringType); ok {
			return
		}
		if array, ok := typ.(*typechecker.ArrayType); ok && (array.IsSlice || array.IsSpan) {
			if !env.ContainsBorrowStorage(array.ElementType) {
				return
			}
		}
	}
	if !env.ContainsBorrowStorage(typ) {
		return
	}
	d := bc.reportBorrow(origin, CodeBorrowEscape, "cannot store borrowed access in an aggregate without a proven destination lifetime")
	d.AddNote("copying a record, array, or ADT does not copy the storage referenced by its views or spans")
	d.AddHelp("keep the borrow in a direct view/span binding, or store owned data or offsets into caller-owned storage")
}
