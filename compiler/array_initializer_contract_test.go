package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Checking alone cannot establish that an initializer survived parsing: a
// missing initializer can either zero-initialize an ordinary array or trigger
// a sealed-handle construction error for the wrong reason.
func requireMainArrayInitializer(t *testing.T, comp Compilation, name string, elements []string) {
	t.Helper()
	tree, err := comp.Parse().Get()
	if err != nil {
		t.Fatalf("array initializer must parse: %v", err)
	}
	for _, stmt := range tree.Root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name.Value != "main" {
			continue
		}
		body, ok := fn.Body.(*ast.BlockExpression)
		if !ok || body.Block == nil {
			t.Fatalf("main body = %T, want block", fn.Body)
		}
		for _, stmt := range body.Block.Statements {
			decl, ok := stmt.(*ast.VariableDeclaration)
			if !ok || decl.Name.Value != name {
				continue
			}
			array, ok := decl.Value.(*ast.ArrayLiteral)
			if !ok || array == nil {
				t.Fatalf("%s initializer = %T, want retained array literal", name, decl.Value)
			}
			if len(array.Elements) != len(elements) {
				t.Fatalf("%s has %d elements, want %d", name, len(array.Elements), len(elements))
			}
			for i, want := range elements {
				if got := array.Elements[i].String(); got != want {
					t.Errorf("%s element %d = %q, want %q", name, i, got, want)
				}
			}
			return
		}
	}
	t.Fatalf("missing main declaration %s", name)
}

func TestArrayInitializerRetainsMultilineElements(t *testing.T) {
	for _, tc := range []struct {
		name, prefix, elementType, first, second, result string
	}{
		{"primitive", "", "i32", "11", "31", "xs[0] + xs[1]"},
		{"record", "Point: type = struct { x: i32 }\n", "Point", "Point { x: 11 }", "Point { x: 31 }", "xs[0].x + xs[1].x"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			src := tc.prefix + "main: (): i32 = {\n xs: [2]" + tc.elementType + " = [\n" + tc.first + ",\n" + tc.second + "\n]\n" + tc.result + "\n}"
			comp := New().WithSource(tc.name+".oak", src)
			elements := []string{"11", "31"}
			if tc.name == "record" {
				elements = []string{"{x: 11}", "{x: 31}"}
			}
			requireMainArrayInitializer(t, comp, "xs", elements)
			if err := comp.Check().Err(); err != nil {
				t.Fatalf("valid multiline array must check: %v", err)
			}
			if code, abnormal := buildAndRun(t, "multiline_array_"+tc.name, src); abnormal || code != 42 {
				t.Fatalf("exit=(%d, abnormal=%v), want 42", code, abnormal)
			}
		})
	}
}

func TestProtocolSealedArrayInitializerContract(t *testing.T) {
	for _, forged := range []bool{false, true} {
		name, first, wantFirst := "legitimate", "seal_handle()", "seal_handle()"
		if forged {
			name, first, wantFirst = "forged", "Seal { data: seal_initial_data() }", "{data: seal_initial_data()}"
		}
		t.Run(name, func(t *testing.T) {
			src := sealedConstructorProtocol + "main: (): i32 = {\n handles: [2]Seal[SealReady] = [\n" + first + ",\n seal_handle()\n]\n 0\n}"
			comp := New().WithSource(name+".oak", src)
			requireMainArrayInitializer(t, comp, "handles", []string{wantFirst, "seal_handle()"})
			err := comp.Check().Err()
			if !forged {
				if err != nil {
					t.Fatalf("constructor array must check: %v", err)
				}
				return
			}
			expectCode(t, name, err, typechecker.CodeResourceTypestateConstruction)
			if !strings.Contains(err.Error(), "a sealed Seal[SealReady] cannot be constructed here; use seal_handle or a checked same-resource transition") {
				t.Fatalf("want nested construction rejection, not zero-initialization rejection: %v", err)
			}
		})
	}
}

func TestArrayInitializerRejectsTrailingComma(t *testing.T) {
	// Array productions currently do not permit trailing separators. In an
	// annotated declaration, a failed literal must not become an absent value.
	for _, tc := range []struct{ name, prefix, declaration string }{
		{"primitive_single", "", "xs: [2]i32 = [11, 31,]"},
		{"primitive_multiline", "", "xs: [2]i32 = [\n11,\n31,\n]"},
		{"record", "Point: type = struct { x: i32 }\n", "xs: [2]Point = [\nPoint { x: 11 },\nPoint { x: 31 },\n]"},
		{"sealed_forged", sealedConstructorProtocol, "handles: [2]Seal[SealReady] = [\nSeal { data: seal_initial_data() },\nseal_handle(),\n]"},
		{"sealed_legitimate", sealedConstructorProtocol, "handles: [2]Seal[SealReady] = [\nseal_handle(),\nseal_handle(),\n]"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			for _, phase := range []struct {
				name string
				run  func(Compilation) error
			}{
				{"Parse", func(comp Compilation) error { return comp.Parse().Err() }},
				{"Check", func(comp Compilation) error { return comp.Check().Err() }},
				{"EmitC", func(comp Compilation) error { return comp.EmitC().Err() }},
			} {
				t.Run(phase.name, func(t *testing.T) {
					comp := New().WithSource(tc.name+".oak", tc.prefix+"main: (): i32 = {\n"+tc.declaration+"\n0\n}")
					if err := phase.run(comp); err == nil || err.Error() != "parse failed: expected value expression after =" {
						t.Errorf("must reject malformed initializer at parsing: %v", err)
					}
				})
			}
		})
	}
}
