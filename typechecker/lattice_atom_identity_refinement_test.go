package typechecker

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	gotypes "go/types"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"testing"

	oakast "github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// This manifest is deliberately exhaustive. A new in-package Type
// implementation or a new field on an existing implementation must choose an
// atom-identity policy before the lattice can consume it as a DecidableEq.
var latticeAtomConstructorTypes = map[string]reflect.Type{
	"PrimitiveType":          reflect.TypeOf(PrimitiveType{}),
	"StringType":             reflect.TypeOf(StringType{}),
	"BoolType":               reflect.TypeOf(BoolType{}),
	"UnitType":               reflect.TypeOf(UnitType{}),
	"NeverType":              reflect.TypeOf(NeverType{}),
	"AnyType":                reflect.TypeOf(AnyType{}),
	"ADTType":                reflect.TypeOf(ADTType{}),
	"NarrowedADTVariantType": reflect.TypeOf(NarrowedADTVariantType{}),
	"RecordType":             reflect.TypeOf(RecordType{}),
	"InterfaceType":          reflect.TypeOf(InterfaceType{}),
	"UnionType":              reflect.TypeOf(UnionType{}),
	"IntersectionType":       reflect.TypeOf(IntersectionType{}),
	"FieldAccessorType":      reflect.TypeOf(FieldAccessorType{}),
	"FunctionType":           reflect.TypeOf(FunctionType{}),
	"ArrayType":              reflect.TypeOf(ArrayType{}),
	"GenericType":            reflect.TypeOf(GenericType{}),
	"TypeVar":                reflect.TypeOf(TypeVar{}),
	"constraintSetType":      reflect.TypeOf(constraintSetType{}),
	"CType":                  reflect.TypeOf(CType{}),
	"SimdType":               reflect.TypeOf(SimdType{}),
	"MmioRegisterType":       reflect.TypeOf(MmioRegisterType{}),
	"BufferType":             reflect.TypeOf(BufferType{}),
	"AtomicType":             reflect.TypeOf(AtomicType{}),
	"CFnType":                reflect.TypeOf(CFnType{}),
	"ConstIntType":           reflect.TypeOf(ConstIntType{}),
}

var latticeAtomConstructorFields = map[string][]string{
	"PrimitiveType":          {"Name", "Refinement"},
	"StringType":             {"Encoding"},
	"BoolType":               {},
	"UnitType":               {},
	"NeverType":              {},
	"AnyType":                {},
	"ADTType":                {"Name"},
	"NarrowedADTVariantType": {"ADTName", "VariantName", "TypeArgs"},
	"RecordType":             {"Fields", "Name", "Order", "Struct", "Open", "Row"},
	"InterfaceType":          {"Name", "Methods"},
	"UnionType":              {"Types"},
	"IntersectionType":       {"Types"},
	"FieldAccessorType":      {"Field"},
	"FunctionType":           {"Parameters", "ReturnType", "Variadic"},
	"ArrayType":              {"ElementType", "Length", "IsSlice", "IsSpan", "Align"},
	"GenericType":            {"Name", "TypeArgs"},
	"TypeVar":                {"Name", "ID", "Monomorphic", "monomorphicGroup"},
	"constraintSetType":      {"Requirements"},
	"CType":                  {"Name"},
	"SimdType":               {"Name"},
	"MmioRegisterType":       {"Width", "Access"},
	"BufferType":             {"Element", "Custody"},
	"AtomicType":             {"Element"},
	"CFnType":                {"Parameters", "ReturnType", "Expr"},
	"ConstIntType":           {"Value"},
}

func TestLatticeAtomIdentityConstructorAndFieldCoverage(t *testing.T) {
	fset := token.NewFileSet()
	packages, err := parser.ParseDir(fset, ".", func(info os.FileInfo) bool {
		return !strings.HasSuffix(info.Name(), "_test.go")
	}, 0)
	if err != nil {
		t.Fatal(err)
	}
	pkg := packages["typechecker"]
	if pkg == nil {
		t.Fatal("go/parser did not find the typechecker package")
	}

	typeImplementers := latticeTypeImplementers(t, fset, pkg)
	switchCases := latticeAtomIdentitySwitchCases(t, fset, pkg)
	wantConstructors := sortedMapKeys(latticeAtomConstructorTypes)
	if got := sortedBoolMapKeys(typeImplementers); !reflect.DeepEqual(got, wantConstructors) {
		t.Fatalf("in-package Type implementations = %v, identity manifest = %v", got, wantConstructors)
	}
	if got := sortedBoolMapKeys(switchCases); !reflect.DeepEqual(got, wantConstructors) {
		t.Fatalf("latticeAtomIdentical explicit cases = %v, Type implementations = %v", got, wantConstructors)
	}

	for _, name := range wantConstructors {
		typeInfo := latticeAtomConstructorTypes[name]
		got := make([]string, typeInfo.NumField())
		for i := 0; i < typeInfo.NumField(); i++ {
			got[i] = typeInfo.Field(i).Name
		}
		want, classified := latticeAtomConstructorFields[name]
		if !classified || !reflect.DeepEqual(got, want) {
			t.Errorf("%s fields = %v, classified identity fields = %v", name, got, want)
		}
	}
}

func TestLatticeTypeImplementersIncludesPromotedMethods(t *testing.T) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "promoted.go", `package typechecker
type Type interface { String() string; Equals(Type) bool }
type Embedded struct{}
func (*Embedded) String() string { return "" }
func (*Embedded) Equals(Type) bool { return false }
type Promoted struct { Embedded }
`, 0)
	if err != nil {
		t.Fatal(err)
	}
	got := sortedBoolMapKeys(latticeTypeImplementers(t, fset, &ast.Package{
		Name:  "typechecker",
		Files: map[string]*ast.File{"promoted.go": file},
	}))
	want := []string{"Embedded", "Promoted"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("promoted Type implementations = %v, want %v", got, want)
	}
}

// latticeTypeImplementers asks go/types for the actual value and pointer
// method sets of every local concrete named type. The synthetic package keeps
// exactly the information relevant to those method sets: local embedding,
// receiver kind, and the signatures of Type's two methods. This catches Type
// implementations acquired through promoted methods without requiring the
// production package's dependency graph to be re-imported by the test.
func latticeTypeImplementers(t *testing.T, productionFset *token.FileSet, pkg *ast.Package) map[string]bool {
	t.Helper()
	typeSpecs := map[string]*ast.TypeSpec{}
	var methods []*ast.FuncDecl
	for _, file := range pkg.Files {
		for _, declaration := range file.Decls {
			switch declaration := declaration.(type) {
			case *ast.GenDecl:
				if declaration.Tok != token.TYPE {
					continue
				}
				for _, spec := range declaration.Specs {
					typeSpec := spec.(*ast.TypeSpec)
					if typeSpec.Assign.IsValid() {
						t.Fatalf("type alias %s is outside the closed Type-implementation audit", typeSpec.Name.Name)
					}
					if typeSpec.TypeParams != nil {
						t.Fatalf("generic named type %s is outside the closed Type-implementation audit", typeSpec.Name.Name)
					}
					typeSpecs[typeSpec.Name.Name] = typeSpec
				}
			case *ast.FuncDecl:
				if declaration.Recv != nil && (declaration.Name.Name == "String" || declaration.Name.Name == "Equals") {
					methods = append(methods, declaration)
				}
			}
		}
	}

	typeSpec := typeSpecs["Type"]
	if typeSpec == nil || !latticeTypeInterfaceIsExact(typeSpec) {
		t.Fatal("Type must remain exactly interface { String() string; Equals(Type) bool }")
	}

	names := sortedMapKeys(typeSpecs)
	var source strings.Builder
	source.WriteString("package latticeaudit\ntype Type interface { String() string; Equals(Type) bool }\n")
	concrete := map[string]bool{}
	for _, name := range names {
		if name == "Type" {
			continue
		}
		spec := typeSpecs[name]
		source.WriteString("type " + name + " ")
		switch underlying := spec.Type.(type) {
		case *ast.StructType:
			concrete[name] = true
			source.WriteString("struct {")
			for _, field := range underlying.Fields.List {
				if len(field.Names) != 0 {
					continue
				}
				source.WriteString(latticeEmbeddedTypeName(t, productionFset, field.Type, typeSpecs) + ";")
			}
			source.WriteString("}\n")
		case *ast.InterfaceType:
			source.WriteString("interface {")
			for _, field := range underlying.Methods.List {
				if len(field.Names) == 0 {
					source.WriteString(latticeEmbeddedTypeName(t, productionFset, field.Type, typeSpecs) + ";")
					continue
				}
				methodName := field.Names[0].Name
				if methodName == "String" || methodName == "Equals" {
					source.WriteString(latticeAuditMethodSignature(methodName, latticeMethodSignatureIsExact(methodName, field.Type.(*ast.FuncType))) + ";")
				}
			}
			source.WriteString("}\n")
		default:
			concrete[name] = true
			source.WriteString("int\n")
		}
	}
	for _, method := range methods {
		receiverName, pointer := latticeMethodReceiver(t, productionFset, method)
		if _, ok := typeSpecs[receiverName]; !ok {
			t.Fatalf("method %s has unknown local receiver %s", method.Name.Name, receiverName)
		}
		receiver := receiverName
		if pointer {
			receiver = "*" + receiver
		}
		exact := latticeMethodSignatureIsExact(method.Name.Name, method.Type)
		source.WriteString("func (" + receiver + ") " + latticeAuditMethodSignature(method.Name.Name, exact))
		if exact {
			if method.Name.Name == "String" {
				source.WriteString(" { return \"\" }\n")
			} else {
				source.WriteString(" { return false }\n")
			}
		} else {
			source.WriteString(" {}\n")
		}
	}

	auditFset := token.NewFileSet()
	auditFile, err := parser.ParseFile(auditFset, "lattice_method_set_audit.go", source.String(), 0)
	if err != nil {
		t.Fatalf("parse method-set audit: %v\n%s", err, source.String())
	}
	auditPackage, err := (&gotypes.Config{}).Check("latticeaudit", auditFset, []*ast.File{auditFile}, nil)
	if err != nil {
		t.Fatalf("type-check method-set audit: %v\n%s", err, source.String())
	}
	typeInterface := auditPackage.Scope().Lookup("Type").Type().Underlying().(*gotypes.Interface)
	implementers := map[string]bool{}
	for name := range concrete {
		typ := auditPackage.Scope().Lookup(name).Type()
		if gotypes.Implements(typ, typeInterface) {
			t.Fatalf("Type implementation %s has a non-pointer method set; latticeAtomIdentical's object-identity fallback is not reflexive for values", name)
		}
		if gotypes.Implements(gotypes.NewPointer(typ), typeInterface) {
			implementers[name] = true
		}
	}
	return implementers
}

func latticeTypeInterfaceIsExact(spec *ast.TypeSpec) bool {
	interfaceType, ok := spec.Type.(*ast.InterfaceType)
	if !ok || len(interfaceType.Methods.List) != 2 {
		return false
	}
	seen := map[string]bool{}
	for _, field := range interfaceType.Methods.List {
		if len(field.Names) != 1 {
			return false
		}
		name := field.Names[0].Name
		function, ok := field.Type.(*ast.FuncType)
		if !ok || !latticeMethodSignatureIsExact(name, function) {
			return false
		}
		seen[name] = true
	}
	return seen["String"] && seen["Equals"]
}

func latticeMethodSignatureIsExact(name string, function *ast.FuncType) bool {
	if function == nil {
		return false
	}
	switch name {
	case "String":
		return latticeFieldListMatches(function.Params) && latticeFieldListMatches(function.Results, "string")
	case "Equals":
		return latticeFieldListMatches(function.Params, "Type") && latticeFieldListMatches(function.Results, "bool")
	default:
		return false
	}
}

func latticeFieldListMatches(list *ast.FieldList, names ...string) bool {
	if len(names) == 0 {
		return list == nil || len(list.List) == 0
	}
	if list == nil || len(list.List) != len(names) {
		return false
	}
	for i, field := range list.List {
		if len(field.Names) > 1 {
			return false
		}
		identifier, ok := field.Type.(*ast.Ident)
		if !ok || identifier.Name != names[i] {
			return false
		}
	}
	return true
}

func latticeAuditMethodSignature(name string, exact bool) string {
	if !exact {
		return name + "(int)"
	}
	if name == "String" {
		return "String() string"
	}
	return "Equals(Type) bool"
}

func latticeEmbeddedTypeName(t *testing.T, fset *token.FileSet, expression ast.Expr, typeSpecs map[string]*ast.TypeSpec) string {
	t.Helper()
	prefix := ""
	if pointer, ok := expression.(*ast.StarExpr); ok {
		prefix = "*"
		expression = pointer.X
	}
	identifier, ok := expression.(*ast.Ident)
	if !ok || typeSpecs[identifier.Name] == nil {
		t.Fatalf("embedded type %s cannot be audited as a local method-set source", formatNode(fset, expression))
	}
	return prefix + identifier.Name
}

func latticeMethodReceiver(t *testing.T, fset *token.FileSet, method *ast.FuncDecl) (string, bool) {
	t.Helper()
	receiver := method.Recv.List[0].Type
	pointer := false
	if star, ok := receiver.(*ast.StarExpr); ok {
		pointer = true
		receiver = star.X
	}
	identifier, ok := receiver.(*ast.Ident)
	if !ok {
		t.Fatalf("method %s has unaudited receiver %s", method.Name.Name, formatNode(fset, receiver))
	}
	return identifier.Name, pointer
}

func latticeAtomIdentitySwitchCases(t *testing.T, fset *token.FileSet, pkg *ast.Package) map[string]bool {
	t.Helper()
	cases := map[string]bool{}
	functionFound := false
	switchFound := false
	for _, file := range pkg.Files {
		for _, declaration := range file.Decls {
			function, ok := declaration.(*ast.FuncDecl)
			if !ok || function.Name.Name != "latticeAtomIdentical" || function.Body == nil {
				continue
			}
			if functionFound {
				t.Fatal("multiple latticeAtomIdentical declarations found")
			}
			functionFound = true
			ast.Inspect(function.Body, func(node ast.Node) bool {
				typeSwitch, ok := node.(*ast.TypeSwitchStmt)
				if !ok {
					return true
				}
				if switchFound {
					t.Fatal("multiple type switches in latticeAtomIdentical are outside the closed audit")
				}
				switchFound = true
				for _, statement := range typeSwitch.Body.List {
					clause := statement.(*ast.CaseClause)
					if len(clause.List) == 0 {
						t.Fatal("latticeAtomIdentical type switch must not contain a default clause; the audited object-identity fallback belongs after the switch")
					}
					for _, expression := range clause.List {
						pointer, ok := expression.(*ast.StarExpr)
						if !ok {
							t.Fatalf("latticeAtomIdentical has unaudited non-pointer type-switch case %s", formatNode(fset, expression))
						}
						name, ok := pointer.X.(*ast.Ident)
						if !ok {
							t.Fatalf("latticeAtomIdentical has unaudited type-switch case %s", formatNode(fset, expression))
						}
						if cases[name.Name] {
							t.Fatalf("latticeAtomIdentical repeats type-switch case %s", name.Name)
						}
						cases[name.Name] = true
					}
				}
				return false
			})
		}
	}
	if !functionFound {
		t.Fatal("latticeAtomIdentical declaration not found")
	}
	if !switchFound {
		t.Fatal("latticeAtomIdentical type switch not found")
	}
	return cases
}

func sortedMapKeys[V any](values map[string]V) []string {
	keys := make([]string, 0, len(values))
	for key := range values {
		keys = append(keys, key)
	}
	sort.Strings(keys)
	return keys
}

func sortedBoolMapKeys(values map[string]bool) []string { return sortedMapKeys(values) }

func formatNode(fset *token.FileSet, node ast.Node) string {
	return fset.Position(node.Pos()).String()
}

type latticeIdentityPair struct {
	name        string
	left, right Type
}

func latticeIdentityCorrespondencePairs() []latticeIdentityPair {
	u8 := &PrimitiveType{Name: "u8"}
	byteType := &PrimitiveType{Name: "byte"}
	boolType := &BoolType{}
	plainSpan := &ArrayType{ElementType: u8, Length: -1, IsSpan: true}
	tv := &TypeVar{Name: "T", ID: 7, Monomorphic: Substitution{}}
	otherTV := &TypeVar{Name: "T", ID: 7, Monomorphic: Substitution{}}
	var nilPrimitiveA *PrimitiveType
	var nilPrimitiveB *PrimitiveType
	var nilString *StringType
	fnExpr := &oakast.FunctionTypeExpression{}

	return []latticeIdentityPair{
		{"nil interface", nil, nil},
		{"nil versus typed nil", nil, nilPrimitiveA},
		{"same typed nil tag", nilPrimitiveA, nilPrimitiveB},
		{"different typed nil tags", nilPrimitiveA, nilString},
		{"primitive alias", u8, byteType},
		{"primitive refinement", u8, &PrimitiveType{Name: "u8", Refinement: "Small"}},
		{"string default", &StringType{}, &StringType{Encoding: "Utf8"}},
		{"string encoding", &StringType{}, &StringType{Encoding: "Ascii"}},
		{"bool", boolType, &BoolType{}},
		{"unit", &UnitType{}, &UnitType{}},
		{"never", &NeverType{}, &NeverType{}},
		{"any", &AnyType{}, &AnyType{}},
		{"adt", &ADTType{Name: "Choice"}, &ADTType{Name: "Choice"}},
		{"adt name", &ADTType{Name: "Choice"}, &ADTType{Name: "Other"}},
		{"narrowed arguments", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{u8}}, &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{byteType}}},
		{"narrowed adt name", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"}, &NarrowedADTVariantType{ADTName: "Other", VariantName: "Left"}},
		{"narrowed variant", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"}, &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Right"}},
		{"narrowed argument type", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{u8}}, &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{boolType}}},
		{"narrowed argument length", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{u8}}, &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{u8, boolType}}},
		{"narrowed argument order", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{u8, boolType}}, &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left", TypeArgs: []Type{boolType, u8}}},
		{"narrowed versus parent", &NarrowedADTVariantType{ADTName: "Choice", VariantName: "Left"}, &ADTType{Name: "Choice"}},
		{"structural record metadata", &RecordType{Fields: map[string]Type{"x": u8}, Name: "Left", Order: []string{"x"}, Row: "r"}, &RecordType{Fields: map[string]Type{"x": byteType}, Name: "Right", Order: []string{"other"}, Row: "s"}},
		{"structural record open", &RecordType{Fields: map[string]Type{"x": u8}}, &RecordType{Fields: map[string]Type{"x": u8}, Open: true}},
		{"structural record missing field", &RecordType{Fields: map[string]Type{"x": u8}}, &RecordType{}},
		{"structural record field name", &RecordType{Fields: map[string]Type{"x": u8}}, &RecordType{Fields: map[string]Type{"y": u8}}},
		{"structural record field type", &RecordType{Fields: map[string]Type{"x": u8}}, &RecordType{Fields: map[string]Type{"x": boolType}}},
		{"structural record empty nominal name", &RecordType{Fields: map[string]Type{"x": u8}}, &RecordType{Fields: map[string]Type{"x": byteType}, Struct: true}},
		{"nominal record ignores shape", &RecordType{Name: "Stored", Struct: true, Fields: map[string]Type{"x": u8}}, &RecordType{Name: "Stored", Struct: true, Open: true, Fields: map[string]Type{"other": boolType}}},
		{"nominal record name", &RecordType{Name: "StoredA", Struct: true}, &RecordType{Name: "StoredB", Struct: true}},
		{"nominal versus structural record", &RecordType{Name: "Stored", Struct: true}, &RecordType{Name: "Stored"}},
		{"unit versus empty record", &UnitType{}, &RecordType{}},
		{"interface methods metadata", &InterfaceType{Name: "Readable", Methods: map[string]*FunctionType{}}, &InterfaceType{Name: "Readable", Methods: map[string]*FunctionType{"read": {ReturnType: u8}}}},
		{"interface name", &InterfaceType{Name: "Readable"}, &InterfaceType{Name: "Writable"}},
		{"union permutation", &UnionType{Types: []Type{u8, boolType}}, &UnionType{Types: []Type{&BoolType{}, byteType}}},
		{"union multiplicity", &UnionType{Types: []Type{u8, u8}}, &UnionType{Types: []Type{u8}}},
		{"intersection permutation", &IntersectionType{Types: []Type{u8, boolType}}, &IntersectionType{Types: []Type{&BoolType{}, byteType}}},
		{"intersection multiplicity", &IntersectionType{Types: []Type{u8, u8}}, &IntersectionType{Types: []Type{u8}}},
		{"field accessor", &FieldAccessorType{Field: "x"}, &FieldAccessorType{Field: "x"}},
		{"field accessor name", &FieldAccessorType{Field: "x"}, &FieldAccessorType{Field: "y"}},
		{"function ordered shape", &FunctionType{Parameters: []Type{u8}, ReturnType: boolType}, &FunctionType{Parameters: []Type{byteType}, ReturnType: &BoolType{}}},
		{"function result", &FunctionType{Parameters: []Type{u8}, ReturnType: u8}, &FunctionType{Parameters: []Type{u8}, ReturnType: boolType}},
		{"function parameter length", &FunctionType{Parameters: []Type{u8}, ReturnType: boolType}, &FunctionType{Parameters: []Type{u8, boolType}, ReturnType: boolType}},
		{"function parameter order", &FunctionType{Parameters: []Type{u8, boolType}, ReturnType: boolType}, &FunctionType{Parameters: []Type{boolType, u8}, ReturnType: boolType}},
		{"function variadic", &FunctionType{Parameters: []Type{u8}, ReturnType: boolType}, &FunctionType{Parameters: []Type{u8}, ReturnType: boolType, Variadic: true}},
		{"array alias element", plainSpan, &ArrayType{ElementType: byteType, Length: -1, IsSpan: true}},
		{"array element", plainSpan, &ArrayType{ElementType: boolType, Length: -1, IsSpan: true}},
		{"array length", plainSpan, &ArrayType{ElementType: u8, Length: 4, IsSpan: true}},
		{"array alignment", plainSpan, &ArrayType{ElementType: u8, Length: -1, IsSpan: true, Align: 64}},
		{"array slice flag", plainSpan, &ArrayType{ElementType: u8, Length: -1, IsSlice: true, IsSpan: true}},
		{"array span flag", plainSpan, &ArrayType{ElementType: u8, Length: -1}},
		{"generic arguments", &GenericType{Name: "Option", TypeArgs: []Type{u8}}, &GenericType{Name: "Option", TypeArgs: []Type{byteType}}},
		{"generic name", &GenericType{Name: "Option", TypeArgs: []Type{u8}}, &GenericType{Name: "Result", TypeArgs: []Type{u8}}},
		{"generic argument length", &GenericType{Name: "Result", TypeArgs: []Type{u8}}, &GenericType{Name: "Result", TypeArgs: []Type{u8, boolType}}},
		{"generic argument order", &GenericType{Name: "Result", TypeArgs: []Type{u8, boolType}}, &GenericType{Name: "Result", TypeArgs: []Type{boolType, u8}}},
		{"type variable same pointer", tv, tv},
		{"type variable distinct pointer", tv, otherTV},
		{"constraint order", &constraintSetType{Requirements: []string{"Read", "Write"}}, &constraintSetType{Requirements: []string{"Write", "Read"}}},
		{"c type", &CType{Name: "UInt8"}, &CType{Name: "UInt8"}},
		{"c type name", &CType{Name: "UInt8"}, &CType{Name: "Int8"}},
		{"simd", &SimdType{Name: "U8x16"}, &SimdType{Name: "U8x16"}},
		{"simd name", &SimdType{Name: "U8x16"}, &SimdType{Name: "U16x8"}},
		{"mmio", &MmioRegisterType{Width: semir.Mmio32, Access: semir.MmioReadOnly}, &MmioRegisterType{Width: semir.Mmio32, Access: semir.MmioReadOnly}},
		{"mmio width", &MmioRegisterType{Width: semir.Mmio32, Access: semir.MmioReadOnly}, &MmioRegisterType{Width: semir.Mmio64, Access: semir.MmioReadOnly}},
		{"mmio access", &MmioRegisterType{Width: semir.Mmio32, Access: semir.MmioReadOnly}, &MmioRegisterType{Width: semir.Mmio32, Access: semir.MmioReadWrite}},
		{"buffer default custody", &BufferType{Element: u8}, &BufferType{Element: byteType, Custody: HostCustody}},
		{"buffer element", &BufferType{Element: u8}, &BufferType{Element: boolType}},
		{"buffer custody", &BufferType{Element: u8}, &BufferType{Element: u8, Custody: "Device"}},
		{"atomic", &AtomicType{Element: u8}, &AtomicType{Element: byteType}},
		{"atomic element", &AtomicType{Element: u8}, &AtomicType{Element: boolType}},
		{"c function expression metadata", &CFnType{Parameters: []Type{&CType{Name: "UInt8"}}, ReturnType: u8}, &CFnType{Parameters: []Type{&CType{Name: "UInt8"}}, ReturnType: byteType, Expr: fnExpr}},
		{"c function parameter type", &CFnType{Parameters: []Type{u8}, ReturnType: u8}, &CFnType{Parameters: []Type{boolType}, ReturnType: u8}},
		{"c function parameter length", &CFnType{Parameters: []Type{u8}, ReturnType: u8}, &CFnType{Parameters: []Type{u8, boolType}, ReturnType: u8}},
		{"c function parameter order", &CFnType{Parameters: []Type{u8, boolType}, ReturnType: u8}, &CFnType{Parameters: []Type{boolType, u8}, ReturnType: u8}},
		{"c function result", &CFnType{ReturnType: u8}, &CFnType{ReturnType: boolType}},
		{"const integer", &ConstIntType{Value: 4}, &ConstIntType{Value: 4}},
		{"const integer value", &ConstIntType{Value: 4}, &ConstIntType{Value: 5}},
	}
}

func TestLatticeAtomIdentityMatchesLeanModel(t *testing.T) {
	path := filepath.Join("..", "spec", "lean", "Oak", "TypeLatticeAtomIdentity.lean")
	contents, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	renderer := newLatticeIdentityLeanRenderer()
	seen := map[string]bool{}
	var missing []string
	for _, pair := range latticeIdentityCorrespondencePairs() {
		line := fmt.Sprintf("example : atomIdentical (%s) (%s) = %v",
			renderer.checkerType(t, pair.left), renderer.checkerType(t, pair.right),
			latticeAtomIdentical(pair.left, pair.right))
		if seen[line] {
			continue
		}
		seen[line] = true
		if !strings.Contains(string(contents), line) {
			missing = append(missing, line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d production atom-identity decision(s) are not kernel-pinned in %s:\n%s",
			len(missing), path, strings.Join(missing, "\n"))
	}
}

type latticeIdentityLeanRenderer struct {
	binders map[*TypeVar]uint64
	next    uint64
}

func newLatticeIdentityLeanRenderer() *latticeIdentityLeanRenderer {
	return &latticeIdentityLeanRenderer{binders: map[*TypeVar]uint64{}, next: 1}
}

var latticeIdentityLeanTags = map[string]string{
	"PrimitiveType": ".primitive", "StringType": ".string", "BoolType": ".bool",
	"UnitType": ".unit", "NeverType": ".never", "AnyType": ".any", "ADTType": ".adt",
	"NarrowedADTVariantType": ".narrowedADT", "RecordType": ".record", "InterfaceType": ".interface",
	"UnionType": ".union", "IntersectionType": ".intersection", "FieldAccessorType": ".fieldAccessor",
	"FunctionType": ".function", "ArrayType": ".array", "GenericType": ".generic", "TypeVar": ".typeVar",
	"constraintSetType": ".constraintSet", "CType": ".cType", "SimdType": ".simd", "MmioRegisterType": ".mmio",
	"BufferType": ".buffer", "AtomicType": ".atomic", "CFnType": ".cFn", "ConstIntType": ".constInt",
}

func (renderer *latticeIdentityLeanRenderer) checkerType(t *testing.T, typ Type) string {
	t.Helper()
	if typ == nil {
		return ".nilType"
	}
	value := reflect.ValueOf(typ)
	if value.Kind() == reflect.Ptr && value.IsNil() {
		tag, ok := latticeIdentityLeanTags[value.Type().Elem().Name()]
		if !ok {
			t.Fatalf("no Lean typed-nil tag for %s", value.Type())
		}
		return ".typedNil " + tag
	}
	key := func(child Type) string { return "(identityKey (" + renderer.checkerType(t, child) + "))" }
	keys := func(children []Type) string {
		parts := make([]string, len(children))
		for i, child := range children {
			parts[i] = key(child)
		}
		return "[" + strings.Join(parts, ", ") + "]"
	}
	quote := strconv.Quote
	boolean := func(value bool) string { return strconv.FormatBool(value) }
	integer := func(value int64) string { return fmt.Sprintf("(%d : Int)", value) }

	switch typ := typ.(type) {
	case *PrimitiveType:
		return fmt.Sprintf(".primitive %s %s", quote(typ.Name), quote(typ.Refinement))
	case *StringType:
		return fmt.Sprintf(".string %s", quote(typ.Encoding))
	case *BoolType:
		return ".bool"
	case *UnitType:
		return ".unit"
	case *NeverType:
		return ".never"
	case *AnyType:
		return ".any"
	case *ADTType:
		return fmt.Sprintf(".adt %s", quote(typ.Name))
	case *NarrowedADTVariantType:
		return fmt.Sprintf(".narrowedADT %s %s %s", quote(typ.ADTName), quote(typ.VariantName), keys(typ.TypeArgs))
	case *RecordType:
		names := make([]string, 0, len(typ.Fields))
		for name := range typ.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
		fields := make([]string, 0, len(names))
		for _, name := range names {
			fields = append(fields, fmt.Sprintf("(%s, %s)", quote(name), key(typ.Fields[name])))
		}
		order := make([]string, len(typ.Order))
		for i, name := range typ.Order {
			order[i] = quote(name)
		}
		return fmt.Sprintf(".record [%s] %s [%s] %s %s %s", strings.Join(fields, ", "), quote(typ.Name), strings.Join(order, ", "), boolean(typ.Struct), boolean(typ.Open), quote(typ.Row))
	case *InterfaceType:
		return fmt.Sprintf(".interface %s %d", quote(typ.Name), len(typ.Methods))
	case *UnionType:
		return fmt.Sprintf(".union %s", keys(typ.Types))
	case *IntersectionType:
		return fmt.Sprintf(".intersection %s", keys(typ.Types))
	case *FieldAccessorType:
		return fmt.Sprintf(".fieldAccessor %s", quote(typ.Field))
	case *FunctionType:
		return fmt.Sprintf(".function %s %s %s", keys(typ.Parameters), key(typ.ReturnType), boolean(typ.Variadic))
	case *ArrayType:
		return fmt.Sprintf(".array %s %s %s %s %d", key(typ.ElementType), integer(typ.Length), boolean(typ.IsSlice), boolean(typ.IsSpan), typ.Align)
	case *GenericType:
		return fmt.Sprintf(".generic %s %s", quote(typ.Name), keys(typ.TypeArgs))
	case *TypeVar:
		binder, ok := renderer.binders[typ]
		if !ok {
			binder = renderer.next
			renderer.next++
			renderer.binders[typ] = binder
		}
		group := 0
		if typ.monomorphicGroup != nil {
			group = 1
		}
		return fmt.Sprintf(".typeVar %d %s %s %d %d", binder, quote(typ.Name), integer(int64(typ.ID)), len(typ.Monomorphic), group)
	case *constraintSetType:
		requirements := make([]string, len(typ.Requirements))
		for i, requirement := range typ.Requirements {
			requirements[i] = quote(requirement)
		}
		return fmt.Sprintf(".constraintSet [%s]", strings.Join(requirements, ", "))
	case *CType:
		return fmt.Sprintf(".cType %s", quote(typ.Name))
	case *SimdType:
		return fmt.Sprintf(".simd %s", quote(typ.Name))
	case *MmioRegisterType:
		return fmt.Sprintf(".mmio %d %s", typ.Width, quote(string(typ.Access)))
	case *BufferType:
		return fmt.Sprintf(".buffer %s %s", key(typ.Element), quote(typ.Custody))
	case *AtomicType:
		return fmt.Sprintf(".atomic %s", key(typ.Element))
	case *CFnType:
		expr := 0
		if typ.Expr != nil {
			expr = 1
		}
		return fmt.Sprintf(".cFn %s %s %d", keys(typ.Parameters), key(typ.ReturnType), expr)
	case *ConstIntType:
		return fmt.Sprintf(".constInt %s", integer(typ.Value))
	default:
		t.Fatalf("no closed-universe Lean renderer for %T", typ)
		return ""
	}
}
