package borrowchecker

import (
	"strings"

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

// aggregateBorrow is one borrow a record binding carries: the field path
// that holds it and the borrow it reproduces.
type aggregateBorrow struct {
	path   string
	owner  string
	kind   borrowKind
	region *Region
	origin ast.Node
}

// bindAggregateBorrows admits a local record binding whose type carries
// views or spans (docs/spec/50-borrowing.md, "Borrows inside aggregates"):
// the value must be a record literal whose borrow-carrying fields are each
// view(&owner) or span(&owner) of an owner in scope, a tracked read-only
// view binding (a local view or a view parameter), or a nested record
// literal of the same shape — or a binding already admitted this way, whose
// borrows the copy reproduces. The binding then borrows every such owner
// under a per-field name (binding.field), so owner exclusivity and lexical
// scope apply exactly as for a direct view or span binding, and every escape
// rule keeps the record itself in place: it is not returned, stored,
// reassigned, or passed to a function, and its borrow fields are not
// reassigned (OAK-B0109 in each case). Reports false when the value's
// borrows cannot be accounted for; the caller then fails closed.
func (bc *BorrowChecker) bindAggregateBorrows(name string, declared typechecker.Type, value ast.Expression, env *typechecker.TypeEnvironment) bool {
	if value == nil || declared == nil {
		return false
	}
	if _, isRecord := declared.(*typechecker.RecordType); !isRecord || !env.ContainsBorrowStorage(declared) {
		return false
	}
	var borrows []aggregateBorrow
	if !bc.collectAggregateBorrows(name, value, env, &borrows) {
		return false
	}
	for _, borrow := range borrows {
		if borrow.kind == BorrowSpan {
			bc.createSpanBorrowWithRegion(borrow.owner, borrow.path, borrow.region, borrow.origin)
		} else {
			bc.createViewBorrowWithRegion(borrow.owner, borrow.path, borrow.region, borrow.origin)
		}
	}
	return true
}

// collectAggregateBorrows gathers the borrows a record value carries under
// the given path prefix; false when one cannot be accounted for.
func (bc *BorrowChecker) collectAggregateBorrows(path string, value ast.Expression, env *typechecker.TypeEnvironment, borrows *[]aggregateBorrow) bool {
	switch v := value.(type) {
	case *ast.RecordLiteral:
		for _, field := range v.FieldOrder {
			fieldType := env.CheckedExpressionType(field.Value)
			if fieldType == nil || !env.ContainsBorrowStorage(fieldType) {
				continue
			}
			// Only view and span fields (and nested records of them) are
			// admitted; a string or any other borrow-carrying type keeps
			// its own storage rules and fails closed here.
			switch ft := fieldType.(type) {
			case *typechecker.ArrayType:
				if !ft.IsSlice && !ft.IsSpan {
					return false
				}
			case *typechecker.RecordType:
			default:
				return false
			}
			fieldPath := path + "." + field.Name
			switch fv := field.Value.(type) {
			case *ast.InvocationExpression:
				callee, isIdent := fv.Function.(*ast.Identifier)
				if !isIdent || (callee.Value != "view" && callee.Value != "span") || len(fv.Arguments) != 1 {
					return false
				}
				owner := bc.extractOwnerName(fv.Arguments[0])
				if owner == "" {
					return false
				}
				kind := BorrowView
				if callee.Value == "span" {
					kind = BorrowSpan
				}
				*borrows = append(*borrows, aggregateBorrow{path: fieldPath, owner: owner, kind: kind, region: bc.wholeOwnerRegion(owner, env), origin: fv})
			case *ast.Identifier:
				// A tracked read-only view (a local binding or a view
				// parameter) may be shared; a span binding would be a second
				// exclusive path and is not admitted here.
				info, tracked := bc.activeBorrows[fv.Value]
				if !tracked || info.kind != BorrowView {
					return false
				}
				*borrows = append(*borrows, aggregateBorrow{path: fieldPath, owner: info.owner, kind: BorrowView, region: info.region, origin: fv})
			case *ast.RecordLiteral:
				if !bc.collectAggregateBorrows(fieldPath, fv, env, borrows) {
					return false
				}
			default:
				return false
			}
		}
		return true
	case *ast.Identifier:
		// A copy of an admitted record binding reproduces its borrows.
		found := false
		prefix := v.Value + "."
		for borrowName, info := range bc.activeBorrows {
			if !strings.HasPrefix(borrowName, prefix) {
				continue
			}
			if info.kind != BorrowView {
				return false
			}
			*borrows = append(*borrows, aggregateBorrow{path: path + borrowName[len(v.Value):], owner: info.owner, kind: BorrowView, region: info.region, origin: v})
			found = true
		}
		return found
	}
	return false
}

// wholeOwnerRegion is the region of a whole owned array, when its static
// length is known.
func (bc *BorrowChecker) wholeOwnerRegion(owner string, env *typechecker.TypeEnvironment) *Region {
	if scheme, ok := env.Get(owner); ok {
		if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok && arrType.Length >= 0 {
			return &Region{Offset: 0, Length: arrType.Length}
		}
	}
	return nil
}
