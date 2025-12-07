package typechecker

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// parseTestCases splits a test file into individual test cases based on numbered comments
func parseTestCases(content string) []testCase {
	var cases []testCase
	lines := strings.Split(content, "\n")

	var currentCase strings.Builder
	var currentNum int
	var currentDesc string
	var expectedError string
	inCase := false

	for i, line := range lines {
		trimmed := strings.TrimSpace(line)

		// Check for test case start (numbered comment like "// 1. Description")
		if strings.HasPrefix(trimmed, "// ") && len(trimmed) > 3 {
			rest := trimmed[3:]
			// Check if it's a numbered test case (e.g., "1. Description")
			if len(rest) > 0 && rest[0] >= '0' && rest[0] <= '9' {
				// Save previous case if any
				if inCase && currentCase.Len() > 0 {
					code := strings.TrimSpace(currentCase.String())
					// Remove EXPECT_TYPE_ERROR comments from code
					codeLines := strings.Split(code, "\n")
					var cleanCode []string
					for _, cl := range codeLines {
						if !strings.Contains(cl, "EXPECT_TYPE_ERROR:") {
							cleanCode = append(cleanCode, cl)
						}
					}
					code = strings.Join(cleanCode, "\n")

					if code != "" {
						cases = append(cases, testCase{
							number:        currentNum,
							description:   currentDesc,
							code:          code,
							expectedError: expectedError,
						})
					}
					currentCase.Reset()
					expectedError = ""
				}

				// Parse new test case number and description
				parts := strings.SplitN(rest, ".", 2)
				if len(parts) == 2 {
					currentNum = 0
					// Try to parse number
					for _, c := range parts[0] {
						if c >= '0' && c <= '9' {
							currentNum = currentNum*10 + int(c-'0')
						}
					}
					currentDesc = strings.TrimSpace(parts[1])
				} else {
					currentDesc = rest
				}
				inCase = true
				continue
			}

			// Check for EXPECT_TYPE_ERROR comment
			if strings.Contains(trimmed, "EXPECT_TYPE_ERROR:") {
				parts := strings.SplitN(trimmed, "EXPECT_TYPE_ERROR:", 2)
				if len(parts) == 2 {
					expectedError = strings.TrimSpace(parts[1])
				}
				continue
			}
		}

		// Add line to current case
		if inCase {
			if currentCase.Len() > 0 {
				currentCase.WriteString("\n")
			}
			currentCase.WriteString(line)
		}

		// If this is the last line and we have a case, save it
		if i == len(lines)-1 && inCase && currentCase.Len() > 0 {
			code := strings.TrimSpace(currentCase.String())
			// Remove EXPECT_TYPE_ERROR comments from code
			codeLines := strings.Split(code, "\n")
			var cleanCode []string
			for _, cl := range codeLines {
				if !strings.Contains(cl, "EXPECT_TYPE_ERROR:") {
					cleanCode = append(cleanCode, cl)
				}
			}
			code = strings.Join(cleanCode, "\n")

			if code != "" {
				cases = append(cases, testCase{
					number:        currentNum,
					description:   currentDesc,
					code:          code,
					expectedError: expectedError,
				})
			}
		}
	}

	return cases
}

type testCase struct {
	number        int
	description   string
	code          string
	expectedError string // For negative tests
}

// TestTypeChecker_ZooFileExists verifies the test file exists
func TestTypeChecker_ZooFileExists(t *testing.T) {
	wd, _ := os.Getwd()
	testFile := filepath.Join(wd, "testdata", "typecheck_positive.oak")
	if _, err := os.Stat(testFile); os.IsNotExist(err) {
		testFile = filepath.Join("typechecker", "testdata", "typecheck_positive.oak")
		if _, err := os.Stat(testFile); os.IsNotExist(err) {
			t.Fatalf("Test file not found: %s (cwd: %s)", testFile, wd)
		}
	}
	t.Logf("Test file found: %s", testFile)
}

// TestTypeChecker_PositiveCases tests all positive cases from typecheck_positive.oak
func TestTypeChecker_PositiveCases(t *testing.T) {
	// Read the test file
	wd, _ := os.Getwd()
	testFile := filepath.Join(wd, "testdata", "typecheck_positive.oak")
	if _, err := os.Stat(testFile); os.IsNotExist(err) {
		// Try relative to package
		testFile = filepath.Join("typechecker", "testdata", "typecheck_positive.oak")
	}

	content, err := os.ReadFile(testFile)
	if err != nil {
		t.Fatalf("Failed to read test file %s: %v (cwd: %s)", testFile, err, wd)
	}

	cases := parseTestCases(string(content))

	if len(cases) == 0 {
		t.Fatalf("No test cases found in typecheck_positive.oak (file length: %d bytes, path: %s)", len(content), testFile)
	}

	t.Logf("Found %d test cases in typecheck_positive.oak", len(cases))

	for _, tc := range cases {
		if tc.code == "" {
			continue // Skip empty cases
		}

		name := tc.description
		if name == "" {
			name = fmt.Sprintf("case_%d", tc.number)
		}

		t.Run(name, func(t *testing.T) {
			testCase := tc // Avoid shadowing
			program := parseProgram(testCase.code)
			if program == nil {
				t.Fatalf("Failed to parse program for case %d", testCase.number)
			}

			typeChecker := setupTypeChecker(testCase.code)
			typeChecker.CheckProgram(program)

			errors := typeChecker.Errors()
			if len(errors) > 0 {
				t.Errorf("Expected no type errors, but got %d:\n%s", len(errors), strings.Join(errors, "\n"))
			}
		})
	}
}

// TestTypeChecker_NegativeCases tests all negative cases from typecheck_negative.oak
func TestTypeChecker_NegativeCases(t *testing.T) {
	// Read the test file
	wd, _ := os.Getwd()
	testFile := filepath.Join(wd, "testdata", "typecheck_negative.oak")
	if _, err := os.Stat(testFile); os.IsNotExist(err) {
		// Try relative to package
		testFile = filepath.Join("typechecker", "testdata", "typecheck_negative.oak")
	}

	content, err := os.ReadFile(testFile)
	if err != nil {
		t.Fatalf("Failed to read test file %s: %v (cwd: %s)", testFile, err, wd)
	}

	cases := parseTestCases(string(content))

	if len(cases) == 0 {
		t.Fatal("No test cases found in typecheck_negative.oak")
	}

	for _, tc := range cases {
		if tc.code == "" {
			continue // Skip empty cases
		}

		name := tc.description
		if name == "" {
			name = fmt.Sprintf("case_%d", tc.number)
		}

		t.Run(name, func(t *testing.T) {
			testCase := tc // Avoid shadowing
			program := parseProgram(testCase.code)
			if program == nil {
				// Parser errors are acceptable for some negative cases
				t.Logf("Parser failed for case %d (may be expected)", testCase.number)
				return
			}

			typeChecker := setupTypeChecker(testCase.code)
			typeChecker.CheckProgram(program)

			errors := typeChecker.Errors()
			if len(errors) == 0 {
				t.Errorf("Expected type error containing '%s', but got no errors", testCase.expectedError)
				return
			}

			// Check if any error contains the expected substring
			found := false
			errorText := strings.Join(errors, " | ")
			if strings.Contains(errorText, testCase.expectedError) {
				found = true
			} else {
				// Try case-insensitive match
				if strings.Contains(strings.ToLower(errorText), strings.ToLower(testCase.expectedError)) {
					found = true
				}
			}

			if !found {
				t.Errorf("Expected error containing '%s', but got:\n%s", testCase.expectedError, errorText)
			}
		})
	}
}
