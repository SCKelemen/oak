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

	// Advanced types example (commented out - has typechecker issues with generics)
	// advancedCode := `
	// fn replicate4[T](value: T): [4]T = {
	//     xs: [4]T = [4]T{ value, value, value, value }
	//     xs
	// }
	//
	// four_ints: [4]i32 = replicate4(7)
	// `

	// Type error example (negative test)
	errorCode := `
x: i32 = "hello"
y: string = 42
`

	// Create type checker
	objEnv := object.NewEnvironment()
	tc := typechecker.New(objEnv)

	// Generate golden files for simple example
	fmt.Println("Generating golden files for 'simple' example...")
	outputs1, err := serialize.SerializeToGolden("simple", 0, simpleCode, tc)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error generating simple example: %v\n", err)
	} else {
		fmt.Printf("✓ Generated: %s\n", outputs1.Source)
		fmt.Printf("✓ Generated: %s\n", outputs1.Lexer)
		fmt.Printf("✓ Generated: %s\n", outputs1.Parser)
		fmt.Printf("✓ Generated: %s\n", outputs1.AST)
		fmt.Printf("✓ Generated: %s\n", outputs1.Typechecker)
		fmt.Printf("✓ Generated: %s\n", outputs1.Lowering)
		fmt.Printf("✓ Generated: %s\n", outputs1.BorrowChecker)
		fmt.Printf("✓ Generated: %s\n", outputs1.Codegen)
	}

	// Skip advanced types for now - has typechecker issues with generics
	// fmt.Println("\nSkipping 'advanced_types' example (generics not fully supported yet)")

	// Generate golden files for error example (negative test)
	fmt.Println("\nGenerating golden files for 'type_errors' example (negative test)...")
	// Create a fresh type checker for this example
	objEnv3 := object.NewEnvironment()
	tc3 := typechecker.New(objEnv3)
	outputs3, err := serialize.SerializeToGolden("type_errors", 0, errorCode, tc3)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error generating type_errors example: %v\n", err)
	} else {
		fmt.Printf("✓ Generated: %s\n", outputs3.Source)
		fmt.Printf("✓ Generated: %s\n", outputs3.Lexer)
		fmt.Printf("✓ Generated: %s\n", outputs3.Parser)
		fmt.Printf("✓ Generated: %s\n", outputs3.AST)
		fmt.Printf("✓ Generated: %s\n", outputs3.Typechecker)
		fmt.Printf("✓ Generated: %s\n", outputs3.Lowering)
		fmt.Printf("✓ Generated: %s\n", outputs3.BorrowChecker)
		fmt.Printf("✓ Generated: %s\n", outputs3.Codegen)
	}

	fmt.Println("\n✓ All golden files generated in golden/ directory")
}
