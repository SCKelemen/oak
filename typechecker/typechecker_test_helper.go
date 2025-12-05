package typechecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

// Helper functions for tests
// These are defined in a separate file to ensure they're accessible to all test files

func setupTypeChecker(input string) *TypeChecker {
	_ = input // Parameter kept for API consistency with test calls
	env := object.NewEnvironment()
	return New(env)
}

func parseProgram(input string) *ast.Program {
	l := scanner.New(input)
	p := parser.New(l)
	return p.ParseProgram()
}
