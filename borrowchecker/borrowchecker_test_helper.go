package borrowchecker

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// setupBorrowChecker is a helper function for tests that sets up a borrow checker
// with a parsed program and type checker. This is shared across test files.
func setupBorrowCheckerForTest(input string) (*BorrowChecker, *ast.Program, *typechecker.TypeChecker) {
	lxr := scanner.New(input)
	p := parser.New(lxr)
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		// Parser errors - return nil program
		return nil, nil, nil
	}

	// Create object environment for typechecker
	objEnv := object.NewEnvironment()
	tc := typechecker.New(objEnv)
	tc.CheckProgram(program)

	bc := New()
	return bc, program, tc
}
