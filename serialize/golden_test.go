package serialize

import (
	"os"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

func TestSerializeToGolden(t *testing.T) {
	sourceCode := `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`

	// Create type checker
	objEnv := object.NewEnvironment()
	tc := typechecker.New(objEnv)

	// Serialize to golden (baseStageNum=0 means source is stage 0, lexer is 1, etc.)
	outputs, err := SerializeToGolden("test_example", 0, sourceCode, tc)
	if err != nil {
		t.Fatalf("Failed to serialize to golden: %v", err)
	}

	// Verify all output files exist
	files := []string{
		outputs.Source,
		outputs.Lexer,
		outputs.Parser,
		outputs.AST,
		outputs.Typechecker,
		outputs.Lowering,
		outputs.BorrowChecker,
		outputs.Codegen,
	}

	for _, file := range files {
		if _, err := os.Stat(file); os.IsNotExist(err) {
			t.Errorf("Expected golden file does not exist: %s", file)
		} else {
			t.Logf("✓ Created: %s", file)
		}
	}

	// Clean up
	defer os.RemoveAll("golden")
}

func TestSerializeToGoldenWithErrors(t *testing.T) {
	// Test with code that will produce type errors
	sourceCode := `
x: i32 = "hello"  // Type error: string assigned to i32
y: string = 42    // Type error: int assigned to string
`

	objEnv := object.NewEnvironment()
	tc := typechecker.New(objEnv)

	// Serialize to golden (should capture errors) (baseStageNum=0)
	outputs, err := SerializeToGolden("test_errors", 0, sourceCode, tc)
	if err != nil {
		t.Fatalf("Failed to serialize to golden: %v", err)
	}

	// Verify error files exist
	if _, err := os.Stat(outputs.Typechecker); os.IsNotExist(err) {
		t.Errorf("Typechecker output should exist even with errors: %s", outputs.Typechecker)
	}

	// Read typechecker output to verify errors were captured
	objects, err := ReadJSONLFile(outputs.Typechecker)
	if err != nil {
		t.Fatalf("Failed to read typechecker output: %v", err)
	}

	// Should have error entries
	hasErrors := false
	for _, obj := range objects {
		if objMap, ok := obj.(map[string]interface{}); ok {
			if objType, ok := objMap["type"].(string); ok && objType == "error" {
				hasErrors = true
				t.Logf("Captured error: %v", objMap["message"])
			}
		}
	}

	if !hasErrors {
		t.Error("Expected to find errors in typechecker output, but none found")
	}

	// Clean up
	defer os.RemoveAll("golden")
}
