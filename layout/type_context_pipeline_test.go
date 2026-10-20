package layout_test

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
)

func TestRecordCallableFieldsPublicPipeline(t *testing.T) {
	for name, source := range map[string]string{
		"struct":          "R: type = struct {\n  get: () -> u32\n    size: u32\n}\n",
		"semantic record": "R: type = {\n  get: () -> u32\n    size: u32\n}\n",
		"generic struct":  "R[T]: type = struct {\n  get: () -> T\n    size: u32\n}\n",
		"field effects":   "R: type = struct {\n  get: () -> u32 effects { }\n    size: u32\n}\n",
	} {
		t.Run(name, func(t *testing.T) {
			tree, err := compiler.New().WithSource("record-layout.oak", source).Parse().Get()
			if err != nil {
				t.Fatal(err)
			}
			if len(tree.Root.Statements) != 1 {
				t.Fatalf("fields escaped record: %d top-level statements", len(tree.Root.Statements))
			}
			declaration := tree.Root.Statements[0].(*ast.ADTType)
			record := declaration.Variants[0].Literal.(*ast.RecordLiteral)
			if len(record.FieldOrder) != 2 || record.FieldOrder[0].Name != "get" || record.FieldOrder[1].Name != "size" {
				t.Fatalf("lost ordered fields: %#v", record.FieldOrder)
			}
			callable, ok := record.FieldOrder[0].Value.(*ast.FunctionTypeExpression)
			if !ok || len(callable.Parameters) != 0 {
				t.Fatalf("get ceased to be a nullary function type: %#v", record.FieldOrder[0].Value)
			}
			if callable.EffectsDeclared != (name == "field effects") {
				t.Fatalf("field effect row changed: %#v", callable)
			}
		})
	}
}

func TestLocalCallableLayoutPublicPipeline(t *testing.T) {
	for _, source := range []string{
		"f: (): u32 {\n  g: (): u32\n    42\n  g()\n}",
		"f: (): u32\n  g: (): u32\n    42\n  g()\n",
	} {
		tree, err := compiler.New().WithSource("local-layout.oak", source).Parse().Get()
		if err != nil {
			t.Fatal(err)
		}
		outer := tree.Root.Statements[0].(*ast.FunctionStatement).Body.(*ast.BlockExpression)
		if len(outer.Block.Statements) != 2 {
			t.Fatalf("local body escaped its function: %#v", outer.Block.Statements)
		}
		inner, ok := outer.Block.Statements[0].(*ast.FunctionStatement)
		if !ok || inner.Body == nil {
			t.Fatalf("lost local function body: %#v", outer.Block.Statements[0])
		}
	}
}
