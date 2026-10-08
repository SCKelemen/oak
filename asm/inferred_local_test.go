package asm

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func inferredFunction(t *testing.T, source string) *ast.FunctionStatement {
	t.Helper()
	fn, err := parseSignatureWithBody(source)
	if err != nil {
		t.Fatal(err)
	}
	return fn
}

func TestInferredLocalPrimitiveSourceTypes(t *testing.T) {
	for _, tc := range []struct {
		name, params, value string
		width               int
		signed              bool
	}{
		{"unsigned", "a, b: u32", "a | b", 32, false},
		{"signed", "a, b: i16", "a + b", 16, true},
		{"bool", "a, b: Bool", "a && !b", 1, false},
		{"comparison", "a, b: i64", "a < b", 1, false},
		{"constructor", "", "u8(255)", 8, false},
		{"wide", "", "u64(18446744073709551615)", 64, false},
		{"boolean literal", "", "true", 1, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			fn := inferredFunction(t, "f: ("+tc.params+"): Bool { x := "+tc.value+"; true }")
			decl := fn.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration)
			lo := newLowering(fn)
			typ, ok := lo.inferredLocalType(decl.Value)
			width, signed, valid := contractBits(typ)
			if !ok || !valid || width != tc.width || signed != tc.signed {
				t.Fatalf("type=%v ok=%v", typ, ok)
			}
			if _, _, _, ok := ExportSyntax(fn, nil, Declarations{}); ok {
				t.Fatal("inferred source syntax export must remain closed pending independent Oak parity")
			}
			if reason, ok := lo.declareLocal(decl); !ok {
				t.Fatal(reason)
			}
			if decl.Type != nil {
				t.Fatal("source AST annotation was changed")
			}
		})
	}
}

func TestInferredLocalRejectsAmbiguousAndForgedTypes(t *testing.T) {
	for _, tc := range []struct{ name, params, value string }{
		{"default integer", "", "42"},
		{"default float", "", "1.5"},
		{"mixed width", "a: u32, b: u64", "a | b"},
		{"mixed signedness", "a: u32, b: i32", "a + b"},
		{"signed bitwise", "a, b: i32", "a | b"},
		{"bool arithmetic", "a, b: Bool", "a + b"},
		{"constructor overflow", "", "u8(256)"},
		{"wide signed overflow", "", "i64(18446744073709551615)"},
		{"constructor different type", "a: u64", "u32(a)"},
		{"constructor local shadow", "u32: u64", "u32(42)"},
		{"untyped arithmetic", "a: u32", "a + 1"},
		{"unknown binding", "", "missing"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			fn := inferredFunction(t, "f: ("+tc.params+"): Bool { x := "+tc.value+"; true }")
			decl := fn.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration)
			if _, ok := newLowering(fn).inferredLocalType(decl.Value); ok {
				t.Fatal("forged or ambiguous source type accepted")
			}
			if _, _, _, ok := ExportSyntax(fn, nil, Declarations{}); ok {
				t.Fatal("syntax accepted forged or ambiguous source type")
			}
		})
	}
	for _, kind := range []string{"function", "record", "adt"} {
		t.Run("constructor "+kind+" shadow", func(t *testing.T) {
			fn := inferredFunction(t, "f: (): Bool { x := u32(42); true }")
			lo := newLowering(fn)
			decls := Declarations{}
			switch kind {
			case "function":
				lo.functions = map[string]*ast.FunctionStatement{"u32": {}}
			case "record":
				lo.records = map[string]*ast.RecordLiteral{"u32": {}}
				decls.Records = lo.records
			case "adt":
				lo.adts = map[string]*ast.ADTType{"u32": {}}
				decls.ADTs = lo.adts
			}
			decl := fn.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration)
			if _, ok := lo.inferredLocalType(decl.Value); ok {
				t.Fatal("shadowed constructor accepted")
			}
			if _, _, _, ok := ExportSyntax(fn, lo.functions, decls); ok {
				t.Fatal("syntax accepted shadowed constructor")
			}
		})
	}
}

func TestInferredLocalVerificationRetainsSemanticComparison(t *testing.T) {
	decl := "f: (a, b: u32) -> u32"
	machine := "bind w0 = a\nbind w1 = b\norr w0, w0, w1\nret"
	for _, body := range []string{
		"{ x := a | b; x }",
		"{ x := a; x = x | b; x }",
		"{ x := a | b; true ? { y := x; y } | x }",
	} {
		if v := verifyCase(t, decl, body, machine); v.Kind != VerdictProven {
			t.Fatalf("%s: %s %s", body, v.Kind, v.Message)
		}
	}
	if v := verifyCase(t, decl, "{ x := a & b; x }", machine); v.Kind != VerdictMismatch {
		t.Fatalf("changed source must mismatch: %s %s", v.Kind, v.Message)
	}
}

func TestInferredLocalTypeIgnoresStaleTokenPositions(t *testing.T) {
	fn := inferredFunction(t, "f: (a, b: u32): Bool { x := a | b; true }")
	decl := fn.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration)
	expr := decl.Value.(*ast.InfixExpression)
	before := expr.Token
	// Keeping the exact original token is not authority for a changed operand.
	expr.Right = &ast.InvocationExpression{Token: before, Function: &ast.Identifier{Value: "u64", Token: before}, Arguments: []ast.Expression{&ast.IntegerLiteral{Value: 1, Token: before}}}
	if !reflect.DeepEqual(before, expr.Token) {
		t.Fatal("test changed the token")
	}
	if _, ok := newLowering(fn).inferredLocalType(expr); ok {
		t.Fatal("stale token accepted changed source type")
	}
	if _, _, _, ok := ExportSyntax(fn, nil, Declarations{}); ok {
		t.Fatal("syntax accepted stale token authority")
	}
}

func TestInferredLocalLexicalScopeAndCalls(t *testing.T) {
	for _, source := range []string{
		"f: (a: u32): Bool { true ? { hidden := a; true } | true; escaped := hidden; true }",
		"f: (a: u32): Bool { a := u32(1); true }",
		"u32: (): Bool { x := u32(1); true }",
	} {
		fn := inferredFunction(t, source)
		if d := DecideTheorem(fn, nil); d.Kind != DecisionUndecided {
			t.Fatalf("invalid scope admitted: %s: %v", source, d)
		}
		if _, _, _, ok := ExportSyntax(fn, nil, Declarations{}); ok {
			t.Fatalf("syntax admitted invalid scope: %s", source)
		}
	}
	callee := inferredFunction(t, "combine: (a, b: u32): u32 { x := a | b; x }")
	fn := inferredFunction(t, "f: (a, b: u32): Bool { x := a | b; combine(a, b) == x }")
	functions := map[string]*ast.FunctionStatement{"combine": callee}
	if d := DecideTheorem(fn, functions); d.Kind != DecisionProven {
		t.Fatal(d)
	}
	if _, _, _, ok := ExportSyntax(fn, functions, Declarations{}); ok {
		t.Fatal("inferred callee syntax export must remain closed")
	}
	callee.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration).Value.(*ast.InfixExpression).Operator = "&"
	if d := DecideTheorem(fn, functions); d.Kind != DecisionRefuted {
		t.Fatalf("changed callee must refute: %v", d)
	}
}

// Native/shared-Go derivation does not widen the exported syntax contract:
// the independent Oak source serializer has not admitted inferred locals.
func TestInferredLocalSyntaxExportRemainsClosed(t *testing.T) {
	inferred := inferredFunction(t, "f: (a, b: u32): Bool { x := a | b; x == (a | b) }")
	explicit := inferredFunction(t, "f: (a, b: u32): Bool { x: u32 = a | b; x == (a | b) }")
	if _, _, _, ok := ExportSyntax(inferred, nil, Declarations{}); ok {
		t.Fatal("inferred syntax acquired unsupported authority")
	}
	if _, _, why, ok := ExportSyntax(explicit, nil, Declarations{}); !ok {
		t.Fatal(why)
	}
}

func TestInferredLocalBinderScopesFailClosed(t *testing.T) {
	for _, source := range []string{
		"f: (a: u32): Bool = forall (a: u8) { x := a; x == a }",
		"f: (a: u32): Bool = forall (b: u8) { x := b; x == b }",
		"f: (a: u32): Bool = forall (u32: u8) { x := u32(1); true }",
	} {
		fn := inferredFunction(t, source)
		if d := DecideTheorem(fn, nil); d.Kind != DecisionUndecided {
			t.Fatalf("quantified inferred binding admitted: %v", d)
		}
		if _, _, _, ok := ExportSyntax(fn, nil, Declarations{}); ok {
			t.Fatal("syntax admitted quantified inferred binding")
		}
	}
	choice := &ast.ADTType{Name: &ast.Identifier{Value: "Choice"}, Variants: []*ast.ADTVariant{
		{Name: &ast.Identifier{Value: "Some"}, Payload: &ast.Identifier{Value: "u8"}},
		{Name: &ast.Identifier{Value: "None"}},
	}}
	decls := Declarations{ADTs: map[string]*ast.ADTType{"Choice": choice}}
	for _, arm := range []string{
		".Some(a) => { x := a; true } | .None => true",
		".Some(b) => { x := b; true } | .None => true",
		".Some(u32) => { x := u32(1); true } | .None => true",
		"a => { x := a; true }",
	} {
		fn := inferredFunction(t, "f: (a: u32, v: Choice): Bool = v ? | "+arm)
		if d := DecideTheoremWith(fn, nil, nil, decls); d.Kind != DecisionUndecided {
			t.Fatalf("pattern inferred binding admitted: %s: %v", arm, d)
		}
		if _, _, _, ok := ExportSyntax(fn, nil, decls); ok {
			t.Fatalf("syntax admitted pattern inferred binding: %s", arm)
		}
	}
}

func TestInferredLocalPrimitiveNamesRequireUnshadowedBindings(t *testing.T) {
	for _, name := range []string{"u32", "byte", "rune"} {
		for _, kind := range []string{"constant", "record", "adt", "refinement"} {
			for _, value := range []string{"a", name + "(1)"} {
				t.Run(name+"/"+kind+"/"+value, func(t *testing.T) {
					fn := inferredFunction(t, "f: (a: "+name+"): Bool { x := "+value+"; true }")
					lo := newLowering(fn)
					decls := Declarations{}
					switch kind {
					case "constant":
						lo.constants = map[string]Constant{name: {}}
						decls.Constants = lo.constants
					case "record":
						lo.records = map[string]*ast.RecordLiteral{name: {}}
						decls.Records = lo.records
					case "adt":
						lo.adts = map[string]*ast.ADTType{name: {}}
						decls.ADTs = lo.adts
					case "refinement":
						lo.guards = map[string]Guard{name: {}}
						decls.ADTs = map[string]*ast.ADTType{name: {Refinement: &ast.Boolean{Value: true}}}
					}
					value := fn.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration).Value
					if _, ok := lo.inferredLocalType(value); ok {
						t.Fatal("shadowed primitive name acquired type authority")
					}
					if _, _, _, ok := ExportSyntax(fn, nil, decls); ok {
						t.Fatal("syntax accepted shadowed primitive name")
					}
				})
			}
		}
	}
}

func TestInferredLocalRefinementDoesNotUseCallerScope(t *testing.T) {
	fn := inferredFunction(t, "f: (value: u32): Bool = Narrow(u8(1)) == u8(1)")
	predicate := inferredFunction(t, "p: (): Bool { x := value; true }").Body
	guard := Guard{Base: &ast.Identifier{Value: "u8"}, Predicate: predicate}
	if d := DecideTheoremWith(fn, nil, map[string]Guard{"Narrow": guard}, Declarations{}); d.Kind != DecisionUndecided {
		t.Fatalf("refinement captured caller inference: %v", d)
	}
}

func TestInferredLocalCannotUseRetainedShadowBinding(t *testing.T) {
	demonstrated := inferredFunction(t, "f: (a: u32): Bool { true ? { a: u32 = u32(0) } | {}; x := a; x == u32(0) }")
	if d := DecideTheorem(demonstrated, nil); d.Kind != DecisionUndecided {
		t.Fatalf("shadow mutation acquired proof authority: %v", d)
	}

	for _, inner := range []string{"a: u8 = 1", "a: u32 = 1"} {
		fn := inferredFunction(t, "f: (a: u32): Bool { q: Bool = true ? { "+inner+"; true } | true; x := a; x == a }")
		if d := DecideTheorem(fn, nil); d.Kind != DecisionUndecided {
			t.Fatalf("retained inner symbolic binding admitted: %s: %v", inner, d)
		}
	}
}

func TestInferredLocalDuplicateSourceBindersFailClosed(t *testing.T) {
	for _, source := range []string{
		"f: (a: u32, a: u64): Bool { x := a; true }",
		"f: (a: u32, a: u32, a: u32): Bool { x := a; true }",
		"f: (f: u32): Bool { x := f; true }",
	} {
		fn := inferredFunction(t, source)
		if d := DecideTheorem(fn, nil); d.Kind != DecisionUndecided {
			t.Fatalf("ambiguous source binding admitted: %v", d)
		}
	}
}

func TestInferredLocalCannotPrecedeShadowBinding(t *testing.T) {
	fn := inferredFunction(t, "f: (a: u32): Bool { x := a; true ? { a: u32 = u32(0) } | {}; a == u32(0) }")
	if d := DecideTheorem(fn, nil); d.Kind != DecisionUndecided {
		t.Fatalf("later source shadow acquired inferred proof authority: %v", d)
	}
}
