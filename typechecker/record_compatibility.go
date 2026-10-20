package typechecker

// recordUnificationView gives Unit its closed, empty semantic-record view for
// record equations only. Keeping this normalization at admission preserves
// stored types and binder solutions while preventing Unit's broad Equals
// compatibility from erasing an open row. Other constructors have no view.
func recordUnificationView(typ Type) (*RecordType, bool) {
	switch typ := typ.(type) {
	case *RecordType:
		return typ, true
	case *UnitType:
		return &RecordType{}, true
	default:
		return nil, false
	}
}

// recordUnificationAdmissible separates nominal/row admission from field
// equations. Nonempty structs may satisfy semantic shapes, but an empty
// nominal token must never be erased by the vacuous structural equation.
// Row is diagnostic text, not a binder; Open is a semantic distinction.
func recordUnificationAdmissible(left, right *RecordType) bool {
	if left.Open != right.Open {
		return false
	}
	leftNominal := left.Struct && left.Name != ""
	rightNominal := right.Struct && right.Name != ""
	if leftNominal && rightNominal {
		return left.Name == right.Name
	}
	if leftNominal && len(left.Fields) == 0 || rightNominal && len(right.Fields) == 0 {
		return false
	}
	return true
}
