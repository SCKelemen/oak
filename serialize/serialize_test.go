package serialize

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

func TestSerializePipeline(t *testing.T) {
	sourceCode := `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`

	// Create a temporary directory for outputs
	tmpDir := filepath.Join(os.TempDir(), "oak_serialize_test")
	defer os.RemoveAll(tmpDir)

	// Create type checker
	objEnv := object.NewEnvironment()
	tc := typechecker.New(objEnv)

	// Serialize the full pipeline
	outputs, err := SerializePipeline(sourceCode, tmpDir, tc)
	if err != nil {
		t.Fatalf("Failed to serialize pipeline: %v", err)
	}

	// Verify all output files exist
	files := []string{
		outputs.Tokens,
		outputs.AST,
		outputs.LoweredAST,
		outputs.Codegen,
	}

	for _, file := range files {
		if _, err := os.Stat(file); os.IsNotExist(err) {
			t.Errorf("Expected output file does not exist: %s", file)
		}
	}

	t.Logf("Successfully serialized pipeline to %s", tmpDir)
	t.Logf("Tokens: %s", outputs.Tokens)
	t.Logf("AST: %s", outputs.AST)
	t.Logf("Lowered AST: %s", outputs.LoweredAST)
	t.Logf("Codegen: %s", outputs.Codegen)
}

func TestCompareJSONLFiles(t *testing.T) {
	// Create two identical files
	tmpDir := filepath.Join(os.TempDir(), "oak_serialize_compare_test")
	defer os.RemoveAll(tmpDir)

	file1 := filepath.Join(tmpDir, "file1.jsonl")
	file2 := filepath.Join(tmpDir, "file2.jsonl")

	writer1, err := NewJSONLWriter(file1)
	if err != nil {
		t.Fatalf("Failed to create writer1: %v", err)
	}
	writer1.WriteLine(map[string]interface{}{"test": "value", "number": 42})
	writer1.Close()

	writer2, err := NewJSONLWriter(file2)
	if err != nil {
		t.Fatalf("Failed to create writer2: %v", err)
	}
	writer2.WriteLine(map[string]interface{}{"test": "value", "number": 42})
	writer2.Close()

	// Compare identical files
	equal, line1, line2, desc, err := CompareJSONLFiles(file1, file2)
	if err != nil {
		t.Fatalf("Failed to compare files: %v", err)
	}

	if !equal {
		t.Errorf("Files should be equal but comparison returned: line1=%d, line2=%d, desc=%s", line1, line2, desc)
	}
}
