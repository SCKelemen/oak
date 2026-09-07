package typechecker

import (
	"strings"
	"testing"
)

// Typed field tags (docs/spec/40-records.md §12): Go's tag ergonomics,
// statically checked. Namespaces are declared schemas; values typecheck.

const tagSchemas = "json: tag = { name: string, omit: Bool }\npb: tag = { field: u32 }\n\n"

func runTagCheck(t *testing.T, input string) *TypeChecker {
	t.Helper()
	tc := setupTypeChecker(input)
	program := parseProgram(input)
	tc.CheckProgram(program)
	return tc
}

func TestTypedFieldTagsAccepted(t *testing.T) {
	input := tagSchemas + `User: type = struct {
  id(align: 8, json: "user_id", pb: 1): u64
  name(json: { name: "name", omit: true }): u32
}
`
	tc := runTagCheck(t, input)
	if len(tc.Errors()) > 0 {
		t.Fatalf("valid tags rejected: %v", tc.Errors())
	}
	if _, ok := tc.TagSchema("json"); !ok {
		t.Fatal("json schema not registered for projections")
	}
}

func TestUnknownTagNamespaceRejected(t *testing.T) {
	input := tagSchemas + `User: type = struct {
  id(jsn: "user_id"): u64
}
`
	tc := runTagCheck(t, input)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "unknown tag namespace \"jsn\"") {
		t.Fatalf("typo'd namespace must be an error, never silent metadata; got: %v", tc.Errors())
	}
}

func TestTagValueTypeMismatchRejected(t *testing.T) {
	input := tagSchemas + `User: type = struct {
  id(pb: "not a field number"): u64
}
`
	tc := runTagCheck(t, input)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "tag pb.field expects u32") {
		t.Fatalf("tag value must typecheck against the schema, got: %v", tc.Errors())
	}
}

func TestUnknownSchemaFieldRejected(t *testing.T) {
	input := tagSchemas + `User: type = struct {
  id(json: { name: "id", omitempty: true }): u64
}
`
	tc := runTagCheck(t, input)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "tag json has no field omitempty") {
		t.Fatalf("unknown schema field must be rejected, got: %v", tc.Errors())
	}
}

func TestDuplicateTagSchemaRejected(t *testing.T) {
	input := "json: tag = { name: string }\njson: tag = { title: string }\n"
	tc := runTagCheck(t, input)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "already declared") {
		t.Fatalf("duplicate schema must be rejected, got: %v", tc.Errors())
	}
}

func TestTagSchemaFieldTypesRestricted(t *testing.T) {
	input := "weird: tag = { data: [4]u8 }\n"
	tc := runTagCheck(t, input)
	joined := strings.Join(tc.Errors(), "\n")
	if !strings.Contains(joined, "compile-time data") {
		t.Fatalf("non-literal schema field types must be rejected, got: %v", tc.Errors())
	}
}
