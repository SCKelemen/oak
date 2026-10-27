package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"testing"
)

func TestSignatureObligationsRequireIdentity(t *testing.T) {
	fields := map[string]Type{"x": &PrimitiveType{Name: "u8"}}
	nominal := &RecordType{Name: "Stored", Struct: true, Fields: fields}
	shape := &RecordType{Fields: fields}
	cases := []struct {
		name      string
		got, want Type
		accept    bool
	}{
		{"nominal cannot become shape", nominal, shape, false},
		{"shape cannot become nominal", shape, nominal, false},
		{"variant cannot become parent", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "A"}, &ADTType{Name: "Choice"}, false},
		{"parent cannot become variant", &ADTType{Name: "Choice"}, &NarrowedADTVariantType{ADTName: "Choice", VariantName: "A"}, false},
		{"open cannot become closed", &RecordType{Open: true}, &RecordType{}, false},
		{"alignment is not erased", &ArrayType{IsSlice: true, Align: 16, ElementType: &BoolType{}}, &ArrayType{IsSlice: true, ElementType: &BoolType{}}, false},
		{"span authority is not a view", &ArrayType{IsSpan: true, ElementType: &BoolType{}}, &ArrayType{IsSlice: true, ElementType: &BoolType{}}, false},
		{"same nominal identity", nominal, &RecordType{Name: "Stored", Struct: true, Fields: fields}, true},
		{"primitive alias", &PrimitiveType{Name: "byte"}, &PrimitiveType{Name: "u8"}, true},
		{"semantic record names", shape, &RecordType{Name: "ShapeAlias", Fields: fields}, true},
	}
	wrappers := []struct {
		name string
		wrap func(Type) Type
	}{
		{"direct", func(x Type) Type { return x }},
		{"function", func(x Type) Type { return &FunctionType{Parameters: []Type{x}, ReturnType: x} }},
		{"array", func(x Type) Type { return &ArrayType{Length: 2, ElementType: x} }},
		{"generic", func(x Type) Type { return &GenericType{Name: "Box", TypeArgs: []Type{x}} }},
	}
	for _, c := range cases {
		for _, w := range wrappers {
			for _, shared := range []bool{false, true} {
				t.Run(c.name+"/"+w.name+map[bool]string{false: "/value", true: "/shared"}[shared], func(t *testing.T) {
					tc := setupTypeChecker("")
					tc.env.SetType("Actual", w.wrap(c.got))
					tc.env.SetType("Expected", w.wrap(c.want))
					node := &ast.Identifier{Value: "Expected"}
					tc.CheckSignatureObligations([]SignatureObligation{{Internal: "Actual", Member: "member", Type: node, Node: node, TypeMember: shared}})
					if accepted := len(tc.Errors()) == 0; accepted != c.accept {
						t.Fatalf("accepted=%v want %v: %v", accepted, c.accept, tc.Errors())
					}
				})
			}
		}
	}
}
