package typechecker

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
