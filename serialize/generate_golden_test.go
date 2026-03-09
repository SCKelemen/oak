package serialize

import (
	"os"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// TestGenerateGoldenFiles generates golden files for inspection
// Run this test to generate example golden files in the golden/ directory
func TestGenerateGoldenFiles(t *testing.T) {
	if os.Getenv("OAK_GENERATE_GOLDEN") != "1" {
		t.Skip("set OAK_GENERATE_GOLDEN=1 to run golden file generation test")
	}

	testCases := []struct {
		name        string
		sourceCode  string
		description string
	}{
		{
			name: "simple_add",
			sourceCode: `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`,
			description: "Simple arithmetic with variables",
		},
		{
			name: "function_example",
			sourceCode: `
fn add(a: i32, b: i32): i32 = {
    a + b
}

result: i32 = add(3, 4)
`,
			description: "Function definition and call",
		},
		{
			name: "array_example",
			sourceCode: `
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }
first: u8 = arr[0]
slice: []u8 = arr[1:3]
`,
			description: "Array literals, indexing, and slicing",
		},
		{
			name: "type_error",
			sourceCode: `
x: i32 = "hello"  // Type error: string assigned to i32
y: string = 42    // Type error: int assigned to string
`,
			description: "Negative test case with type errors",
		},
		{
			name: "borrow_example",
			sourceCode: `
arr: [4]u8 = [4]u8{ 1, 2, 3, 4 }
view: []u8 = arr[:]
span: [*]u8 = span(&arr)
first: u8 = view[0]
`,
			description: "Borrow checker example with views and spans",
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			t.Logf("Generating golden files for: %s", tc.description)

			// Create a fresh typechecker for each test case
			objEnv := object.NewEnvironment()
			typeChecker := typechecker.New(objEnv)

			outputs, err := SerializeToGolden(tc.name, 0, tc.sourceCode, typeChecker)
			if err != nil {
				t.Fatalf("Failed to generate golden files for %s: %v", tc.name, err)
			}

			t.Logf("✓ Generated golden files:")
			t.Logf("  Source:        %s", outputs.Source)
			t.Logf("  Lexer:         %s", outputs.Lexer)
			t.Logf("  Parser:        %s", outputs.Parser)
			t.Logf("  AST:           %s", outputs.AST)
			t.Logf("  Typechecker:   %s", outputs.Typechecker)
			t.Logf("  Lowering:      %s", outputs.Lowering)
			t.Logf("  BorrowChecker: %s", outputs.BorrowChecker)
			t.Logf("  Codegen:       %s", outputs.Codegen)
		})
	}

	t.Logf("\nAll golden files generated in golden/ directory")
	t.Logf("You can now inspect the files to verify the syntax and format")
}
