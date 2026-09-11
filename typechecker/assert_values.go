package typechecker

// assertOperandName names the type an assert_eq/assert_ne operand has when
// the failure message can print it: the fixed-width integers (aliases and
// the platform-sized names resolve to their width), f32 and f64, and Bool
// (docs/spec/85-discipline.md section 5). Storage floats, records, views,
// and strings are not comparable this way.
func (tc *TypeChecker) assertOperandName(typ Type) (string, bool) {
	switch t := typ.(type) {
	case *BoolType:
		return "Bool", true
	case *PrimitiveType:
		if t.Name == "f32" || t.Name == "f64" {
			return t.Name, true
		}
		if width := tc.FixedWidthName(t.Name); width != "" {
			return width, true
		}
	}
	return "", false
}
