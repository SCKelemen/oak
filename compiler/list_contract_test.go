package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func TestRequiredListAndRecordBoundaryRejectBeforeCompilation(t *testing.T) {
	const pair = "Pair: type = struct { a: i32, b: i32 }\n"
	for _, tc := range []struct{ name, prefix, body, diagnostic string }{
		{"inferred_array_trailing", "", "xs := [u8(1),u8(2),]; 0", "expected list item"},
		{"inferred_array_multiline", "", "xs := [\nu8(1),\nu8(2),\n]; 0", "expected list item"},
		{"typed_inferred_array_trailing", "", "xs := [2]u8{1,2,}; 0", "expected list item"},
		{"inferred_array_empty_item", "", "xs := [u8(1),,u8(2)]; 0", "expected list item"},
		{"inferred_array_leading", "", "xs := [,u8(1),u8(2)]; 0", "expected list item"},
		{"inferred_record_array_trailing", pair, "xs := [Pair {a: 1,b: 3},]; 0", "expected list item"},
		{"inferred_nested_array_trailing", "", "xs := [[u8(1),], [u8(2)]]; 0", "expected list item"},
		{"record_extra_before_comma", pair, "x: Pair = Pair {a: 1 2,b: 3}; x.a", "expected ',' or '}' after record field value"},
		{"record_extra_before_close", pair, "x: Pair = Pair {a: 1,b: 3 4}; x.a", "expected ',' or '}' after record field value"},
		{"record_extra_identifier", pair, "x := Pair {a: 1 extra,b: 3}; x.a", "expected ',' or '}' after record field value"},
		{"record_numeric_suffix", pair, "x := Pair {a: 0u8,b: 3}; x.a", "expected ',' or '}' after record field value"},
		{"record_missing_value", pair, "x := Pair {a: ,b: 3}; x.a", "expected record field value"},
		{"nested_record_extra", pair, "xs := [Pair {a: 1 2,b: 3}]; 0", "expected ',' or '}' after record field value"},
		{"inferred_missing_expression", "", "x := ); 0", "expected value expression after :="},
	} {
		t.Run(tc.name, func(t *testing.T) {
			src := tc.prefix + "main: (): i32 { " + tc.body + " }"
			for _, phase := range []struct {
				name string
				run  func(Compilation) error
			}{
				{"Parse", func(c Compilation) error { return c.Parse().Err() }},
				{"Check", func(c Compilation) error { return c.Check().Err() }},
				{"EmitC", func(c Compilation) error { return c.EmitC().Err() }},
			} {
				t.Run(phase.name, func(t *testing.T) {
					err := phase.run(New().WithSource(tc.name+".oak", src))
					if err == nil || !strings.Contains(err.Error(), "parse failed") || !strings.Contains(err.Error(), tc.diagnostic) {
						t.Fatalf("must reject at parsing with %q: %v", tc.diagnostic, err)
					}
				})
			}
		})
	}
}

func TestRecordBoundaryRetainsNestedRegionFields(t *testing.T) {
	const src = multipleRegionNestedRecordsSource
	tree, err := New().WithSource("nested_regions.oak", src).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	var tag *ast.InvocationExpression
	for _, statement := range tree.Root.Statements {
		fn, ok := statement.(*ast.FunctionStatement)
		if !ok || fn.Name.Value != "pack" {
			continue
		}
		record, ok := fn.Body.(*ast.RecordLiteral)
		if !ok || record.TypeName == nil || record.TypeName.Value != "Envelope" || len(record.OrderedFields()) != 2 {
			t.Fatalf("lost outer record: %#v", fn.Body)
		}
		tag, ok = record.Fields["tag"].(*ast.InvocationExpression)
		if !ok || tag.String() != "u8(0)" {
			t.Fatalf("lost explicit tag type or value: %#v", record.Fields["tag"])
		}
		parts, ok := record.Fields["parts"].(*ast.RecordLiteral)
		if !ok || parts.TypeName == nil || parts.TypeName.Value != "Pair" {
			t.Fatalf("lost nested record: %#v", record.Fields["parts"])
		}
		fields := parts.OrderedFields()
		if len(fields) != 2 || fields[0].Name != "left" || fields[0].Value.String() != "a" || fields[1].Name != "right" || fields[1].Value.String() != "b" {
			t.Fatalf("lost nested fields: %#v", fields)
		}
	}
	if tag == nil {
		t.Fatal("pack function was lost")
	}
	model, err := New().WithSource("nested_regions.oak", src).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	if typ, ok := model.TypeChecker.ExpressionTypeAt(tag.Token); !ok || typ.String() != "u8" {
		t.Fatalf("checked tag type = %v, present=%v; want u8", typ, ok)
	}
	if _, err := New().WithSource("nested_regions.oak", src).EmitC().Get(); err != nil {
		t.Fatal(err)
	}

	// A suffix is a separate identifier, not a typed integer literal. The old
	// record parser discarded it; retaining nested syntax must not restore that.
	invalid := strings.Replace(src, "tag:u8(0)", "tag:0u8", 1)
	for _, phase := range []struct {
		name string
		run  func(Compilation) error
	}{
		{"Parse", func(c Compilation) error { return c.Parse().Err() }},
		{"Check", func(c Compilation) error { return c.Check().Err() }},
		{"EmitC", func(c Compilation) error { return c.EmitC().Err() }},
	} {
		t.Run("invalid_suffix/"+phase.name, func(t *testing.T) {
			err := phase.run(New().WithSource("nested_suffix.oak", invalid))
			if err == nil || !strings.Contains(err.Error(), "parse failed: expected ',' or '}' after record field value") {
				t.Fatalf("numeric suffix must be diagnosed before compilation: %v", err)
			}
		})
	}
}

func TestRequiredListRetainsInferredInitializers(t *testing.T) {
	for _, tc := range []struct {
		name, prefix, literal string
		elements              []string
	}{
		{"primitive", "", "[11,31]", []string{"11", "31"}},
		{"primitive_multiline", "", "[\n11,\n31\n]", []string{"11", "31"}},
		{"typed_primitive", "", "[2]i32{11,31}", []string{"11", "31"}},
		{"record", "Point: type = struct { x: i32 }\n", "[Point {x: 11},Point {x: 31}]", []string{"{x: 11}", "{x: 31}"}},
		{"typed_record", "Point: type = struct { x: i32 }\n", "[2]Point{Point {x: 11},Point {x: 31}}", []string{"{x: 11}", "{x: 31}"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			src := tc.prefix + "main: (): i32 { xs := " + tc.literal + "; 0 }"
			comp := New().WithSource(tc.name+".oak", src)
			requireMainArrayInitializer(t, comp, "xs", tc.elements)
			if err := New().WithSource(tc.name+".oak", src).Check().Err(); err != nil {
				t.Fatalf("valid initializer must check: %v", err)
			}
			if _, err := New().WithSource(tc.name+".oak", src).EmitC().Get(); err != nil {
				t.Fatalf("valid initializer must emit C: %v", err)
			}
		})
	}
}

func TestRecordBoundaryRetainsValidCompleteProgram(t *testing.T) {
	const src = "Pair: type = struct { a: i32, b: i32 }\nmain: (): i32 { x: Pair = Pair {a: 1,b: 3}; x.a }"
	comp := New().WithSource("record_valid.oak", src)
	tree, err := comp.Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	fn := tree.Root.Statements[1].(*ast.FunctionStatement)
	decl := fn.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.VariableDeclaration)
	record, ok := decl.Value.(*ast.RecordLiteral)
	if !ok || record == nil || record.TypeName == nil || record.TypeName.Value != "Pair" {
		t.Fatalf("lost typed record initializer: %#v", decl.Value)
	}
	fields := record.OrderedFields()
	if len(fields) != 2 || fields[0].Name != "a" || fields[0].Value.String() != "1" || fields[1].Name != "b" || fields[1].Value.String() != "3" {
		t.Fatalf("lost ordered values: %#v", fields)
	}
	if err := New().WithSource("record_valid.oak", src).Check().Err(); err != nil {
		t.Fatalf("valid record must check: %v", err)
	}
	if _, err := New().WithSource("record_valid.oak", src).EmitC().Get(); err != nil {
		t.Fatalf("valid record must emit C: %v", err)
	}
}
