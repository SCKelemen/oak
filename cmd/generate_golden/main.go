package main

import (
	"fmt"
	"os"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/serialize"
	"github.com/SCKelemen/oak/typechecker"
)

func main() {
	// Simple example
	simpleCode := `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`

	// Type error example (negative test)
	errorCode := `
x: i32 = "hello"
y: string = 42
`

	// Simple arithmetic and pattern matching
	simpleArithmeticCode := `
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
`

	// Simple function examples
	simpleFunctionCode := `
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
`

	// ADTs with values
	adtWithValuesCode := `
// Simple ADT
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401

// ADT with record literal tags
StatusInfo: type
  = Ok: { code: 200, status: "Okay" }
  | NotFound: { code: 404, status: "Not Found" }
`

	// Package and imports
	packageImportCode := `
package main

import("strings")

str := import("strings")

str2: package = import("strings")

import("strings", "encoding/utf8")
`

	// Comments
	commentsCode := `
// line comment
x: i32 = 5

/* inline comment */
y: i32 = 10

/* multiple 
    line 
    comment
*/
z: i32 = 15
`

	testCases := []struct {
		name       string
		sourceCode string
		skip       bool // Skip if known to have issues
	}{
		{name: "simple", sourceCode: simpleCode},
		{name: "type_errors", sourceCode: errorCode},
		{name: "simple_arithmetic", sourceCode: simpleArithmeticCode},
		{name: "simple_function", sourceCode: simpleFunctionCode},
		{name: "adt_with_values", sourceCode: adtWithValuesCode},
		{name: "package_import", sourceCode: packageImportCode},
		{name: "comments", sourceCode: commentsCode},
	}

	for i, testCase := range testCases {
		if testCase.skip {
			fmt.Printf("Skipping '%s' (known issues)\n", testCase.name)
			continue
		}

		fmt.Printf("Generating golden files for '%s' example...\n", testCase.name)

		// Create a fresh type checker for each test case
		objEnv := object.NewEnvironment()
		tcTypeChecker := typechecker.New(objEnv)

		outputs, err := serialize.SerializeToGolden(testCase.name, 0, testCase.sourceCode, tcTypeChecker)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error generating %s example: %v\n", testCase.name, err)
			if i < len(testCases)-1 {
				fmt.Println("  (Continuing with remaining examples...)")
			}
			continue
		}

		fmt.Printf("✓ Generated: %s\n", outputs.Source)
		fmt.Printf("✓ Generated: %s\n", outputs.Lexer)
		fmt.Printf("✓ Generated: %s\n", outputs.Parser)
		fmt.Printf("✓ Generated: %s\n", outputs.AST)
		fmt.Printf("✓ Generated: %s\n", outputs.Typechecker)
		fmt.Printf("✓ Generated: %s\n", outputs.Lowering)
		fmt.Printf("✓ Generated: %s\n", outputs.BorrowChecker)
		fmt.Printf("✓ Generated: %s\n", outputs.Codegen)
		fmt.Println()
	}

	fmt.Println("✓ All golden files generated in golden/ directory")
}
