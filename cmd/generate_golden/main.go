package main

import (
	"fmt"
	"os"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/serialize"
	"github.com/SCKelemen/oak/typechecker"
)

func main() {
	failed := false
	for _, testCase := range serialize.GoldenCases() {
		if testCase.Skip {
			fmt.Printf("Skipping '%s' (known issues)\n", testCase.Name)
			continue
		}

		fmt.Printf("Generating golden files for '%s'...\n", testCase.Name)

		objEnv := object.NewEnvironment()
		tcTypeChecker := typechecker.New(objEnv)

		outputs, err := serialize.SerializeToGolden(testCase.Name, 0, testCase.SourceCode, tcTypeChecker)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error generating %s: %v\n", testCase.Name, err)
			failed = true
			continue
		}

		for _, path := range []string{
			outputs.Source, outputs.Lexer, outputs.Parser, outputs.AST,
			outputs.Typechecker, outputs.Lowering, outputs.BorrowChecker, outputs.Codegen,
		} {
			fmt.Printf("✓ Generated: %s\n", path)
		}
		fmt.Println()
	}

	if failed {
		fmt.Fprintln(os.Stderr, "❌ Some golden files failed to generate")
		os.Exit(1)
	}
	fmt.Println("✓ All golden files generated in golden/ directory")
}
