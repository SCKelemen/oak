package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/serialize"
	"github.com/SCKelemen/oak/typechecker"
)

func main() {
	// Test cases to verify (must match cmd/generate_golden/main.go)
	testCases := []struct {
		name       string
		sourceCode string
		skip       bool // Skip if known to have issues
	}{
		{
			name: "simple",
			sourceCode: `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`,
		},
		{
			name: "type_errors",
			sourceCode: `
x: i32 = "hello"
y: string = 42
`,
		},
		{
			name: "simple_arithmetic",
			sourceCode: `
// Simple arithmetic
x: i32 = 5 + 3
y: i32 = x * 2

// Pattern matching on integers
result: string = x ?
  | 5 -> "five"
  | 8 -> "eight"
  | _ -> "other"

// ADT definition with value 
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

// Create ADT values
status1: Status = .Ok
status2: Status = .NotFound

// Pattern match on ADT
code: i32 = status1 ?
  | .Ok -> 200
  | .NotFound -> 404
  | _ -> 0
`,
		},
		{
			name: "simple_function",
			sourceCode: `
fn add(a: i32, b: i32): i32
  a + b

fn add2(a: i32, b: i32): i32 = a + b

fn add3(a: i32, b: i32): i32 {
  a + b
}

fn add4(a: i32, b: i32): i32 = { a + b }

x: i32
sum: i32 = add(5, 3)
x = add(4, 2)
x = add(6, 4)
`,
		},
		{
			name: "adt_with_values",
			sourceCode: `
// Simple ADT
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

// ADT with record literal tags
StatusInfo: type
  = Ok: { code: 200, status: "Okay" }
  | NotFound: { code: 404, status: "Not Found" }
`,
		},
		{
			name: "package_import",
			sourceCode: `
package main

import("strings")

str := import("strings")

str2: package = import("strings")

import("strings", "encoding/utf8")
`,
		},
		{
			name: "comments",
			sourceCode: `
// line comment
x: i32 = 5

/* inline comment */
y: i32 = 10

/* multiple 
    line 
    comment
*/
z: i32 = 15
`,
		},
	}

	allPassed := true

	for _, tc := range testCases {
		if tc.skip {
			fmt.Printf("Skipping '%s' (known issues)\n", tc.name)
			continue
		}

		fmt.Printf("Verifying golden files for '%s'...\n", tc.name)

		// Load expected golden files
		expected, err := serialize.LoadGolden(tc.name, 0)
		if err != nil {
			fmt.Fprintf(os.Stderr, "❌ Failed to load expected golden files for %s: %v\n", tc.name, err)
			fmt.Fprintf(os.Stderr, "   (Run 'go run cmd/generate_golden/main.go' to generate them)\n")
			allPassed = false
			continue
		}

		// Generate actual golden files to a temp directory
		tempDir := filepath.Join(os.TempDir(), "oak_golden_verify", tc.name)
		defer os.RemoveAll(tempDir)

		objEnv := object.NewEnvironment()
		tcTypeChecker := typechecker.New(objEnv)

		// Generate to temp directory
		tempGoldenDir := filepath.Join(tempDir, "golden")
		actual, err := serialize.SerializeToGoldenDir(tc.name, 0, tc.sourceCode, tcTypeChecker, tempGoldenDir)
		if err != nil {
			fmt.Fprintf(os.Stderr, "❌ Failed to generate golden files for %s: %v\n", tc.name, err)
			allPassed = false
			continue
		}

		actualTemp := actual

		// Compare each stage
		stages := []struct {
			name     string
			expected string
			actual   string
		}{
			{"lexer", expected.Lexer, actualTemp.Lexer},
			{"parser", expected.Parser, actualTemp.Parser},
			{"typechecker", expected.Typechecker, actualTemp.Typechecker},
			{"borrowchecker", expected.BorrowChecker, actualTemp.BorrowChecker},
		}

		for _, stage := range stages {
			equal, line1, line2, desc, err := serialize.CompareJSONLFiles(stage.expected, stage.actual)
			if err != nil {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: Failed to compare: %v\n", tc.name, stage.name, err)
				allPassed = false
				continue
			}
			if !equal {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: Files differ at line %d/%d: %s\n", tc.name, stage.name, line1, line2, desc)
				allPassed = false
			}
		}

		// Compare JSON files (AST, lowering)
		jsonStages := []struct {
			name     string
			expected string
			actual   string
		}{
			{"ast", expected.AST, actualTemp.AST},
			{"lowering", expected.Lowering, actualTemp.Lowering},
		}

		for _, stage := range jsonStages {
			expectedData, err := os.ReadFile(stage.expected)
			if err != nil {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: Failed to read expected: %v\n", tc.name, stage.name, err)
				allPassed = false
				continue
			}

			actualData, err := os.ReadFile(stage.actual)
			if err != nil {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: Failed to read actual: %v\n", tc.name, stage.name, err)
				allPassed = false
				continue
			}

			// Parse and compare JSON
			var expectedJSON, actualJSON interface{}
			if err := json.Unmarshal(expectedData, &expectedJSON); err != nil {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: Failed to parse expected JSON: %v\n", tc.name, stage.name, err)
				allPassed = false
				continue
			}
			if err := json.Unmarshal(actualData, &actualJSON); err != nil {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: Failed to parse actual JSON: %v\n", tc.name, stage.name, err)
				allPassed = false
				continue
			}

			// Compare as JSON (normalize whitespace)
			expectedNormalized, _ := json.Marshal(expectedJSON)
			actualNormalized, _ := json.Marshal(actualJSON)

			if string(expectedNormalized) != string(actualNormalized) {
				fmt.Fprintf(os.Stderr, "❌ %s/%s: JSON files differ\n", tc.name, stage.name)
				allPassed = false
			}
		}

		// Compare C code (simple string comparison)
		expectedCode, err := os.ReadFile(expected.Codegen)
		if err != nil {
			fmt.Fprintf(os.Stderr, "❌ %s/codegen: Failed to read expected: %v\n", tc.name, err)
			allPassed = false
			continue
		}

		actualCode, err := os.ReadFile(actualTemp.Codegen)
		if err != nil {
			fmt.Fprintf(os.Stderr, "❌ %s/codegen: Failed to read actual: %v\n", tc.name, err)
			allPassed = false
			continue
		}

		if string(expectedCode) != string(actualCode) {
			fmt.Fprintf(os.Stderr, "❌ %s/codegen: C code differs\n", tc.name)
			allPassed = false
		}

		if allPassed {
			fmt.Printf("✅ %s: All golden files match\n", tc.name)
		}
	}

	if !allPassed {
		fmt.Fprintf(os.Stderr, "\n❌ Some golden files do not match expected outputs\n")
		os.Exit(1)
	}

	fmt.Println("\n✅ All golden files match expected outputs")
}
