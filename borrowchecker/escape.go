package borrowchecker

import (
	"sort"

	"github.com/SCKelemen/oak/typechecker"
)

// returnedBorrowKind follows structural storage, not function signatures.
// An owned container does not make its borrowed elements owned. Keep a visited
// set for shared or recursive type graphs and sort record fields so diagnostics
// do not depend on Go map iteration order.
func returnedBorrowKind(typ typechecker.Type, seen map[typechecker.Type]bool) string {
	if typ == nil || seen[typ] {
		return ""
	}
	seen[typ] = true
	switch t := typ.(type) {
	case *typechecker.ArrayType:
		if t.IsSpan {
			return "span"
		}
		if t.IsSlice {
			return "view"
		}
		return returnedBorrowKind(t.ElementType, seen)
	case *typechecker.RecordType:
		names := make([]string, 0, len(t.Fields))
		for name := range t.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			if kind := returnedBorrowKind(t.Fields[name], seen); kind != "" {
				return kind
			}
		}
	case *typechecker.UnionType:
		for _, member := range t.Types {
			if kind := returnedBorrowKind(member, seen); kind != "" {
				return kind
			}
		}
	case *typechecker.IntersectionType:
		for _, member := range t.Types {
			if kind := returnedBorrowKind(member, seen); kind != "" {
				return kind
			}
		}
	}
	return ""
}
