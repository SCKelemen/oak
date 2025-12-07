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
	// Test cases to verify
	testCases := []struct {
		name       string
		sourceCode string
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
	}

	allPassed := true

	for _, tc := range testCases {
		fmt.Printf("Verifying golden files for '%s'...\n", tc.name)

		// Load expected golden files
		expected, err := serialize.LoadGolden(tc.name, 0)
		if err != nil {
			fmt.Fprintf(os.Stderr, "❌ Failed to load expected golden files for %s: %v\n", tc.name, err)
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
