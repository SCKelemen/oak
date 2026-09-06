package discipline

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

// CodeUnboundedLoop records loops without a statically evident bound
// (docs/spec/85-discipline.md section 3, Power of Ten rule 2). The default
// profile surfaces the obligation; the strict profile rejects it.
const CodeUnboundedLoop diagnostic.Code = "OAK-D0103"

// analyzeLoops records an OAK-D0103 obligation for every while loop that
// does not match the canonical bounded counter shape proven by
// Oak.BoundedLoop: `while i < bound` (or <=) advancing i exactly once per
// iteration by a positive constant, with the bound never reassigned in the
// body. The bound fact is recognized, never assumed.
func (r *Result) analyzeLoops(program *ast.Program) {
	if program == nil {
		return
	}
	forEachWhile(program, func(loop *ast.WhileStatement) {
		if boundedWhileShape(loop) {
			return
		}
		d := diagnostic.NewDiagnosticFromNodeWithCode(loop, "discipline", string(CodeUnboundedLoop),
			"loop has no statically evident bound")
		d.Severity = diagnostic.SeverityWarning
		d.AddNote("the strict profile requires every loop to have a statically evident bound (docs/spec/85-discipline.md section 3)")
		d.AddHelp("use the canonical bounded shape — while i < bound with exactly one `i = i + k` step (k a positive constant) and an unmodified bound — or restructure into bounded tail recursion")
		r.diagnostics = append(r.diagnostics, d)
	})
}

// boundedWhileShape recognizes `while i < bound { ... i = i + k ... }`.
func boundedWhileShape(loop *ast.WhileStatement) bool {
	if loop == nil || loop.Body == nil {
		return false
	}
	condition, ok := loop.Condition.(*ast.InfixExpression)
	if !ok || (condition.Operator != "<" && condition.Operator != "<=") {
		return false
	}
	counter, ok := condition.Left.(*ast.Identifier)
	if !ok {
		return false
	}

	// The bound must be fixed: a literal, or an identifier the body never
	// reassigns.
	switch bound := condition.Right.(type) {
	case *ast.IntegerLiteral:
	case *ast.Identifier:
		if bound.Value == counter.Value || countAssignments(loop.Body, bound.Value) != 0 {
			return false
		}
	default:
		return false
	}

	// Exactly one assignment to the counter, advancing it by a positive
	// constant: i = i + k.
	if countAssignments(loop.Body, counter.Value) != 1 {
		return false
	}
	advance := findAssignment(loop.Body, counter.Value)
	if advance == nil {
		return false
	}
	sum, ok := advance.Value.(*ast.InfixExpression)
	if !ok || sum.Operator != "+" {
		return false
	}
	left, ok := sum.Left.(*ast.Identifier)
	if !ok || left.Value != counter.Value {
		return false
	}
	step, ok := sum.Right.(*ast.IntegerLiteral)
	return ok && step.Value >= 1
}

// forEachWhile visits every while statement in the program, including those
// nested in function bodies, blocks, unsafe blocks, and expression blocks.
func forEachWhile(program *ast.Program, visit func(*ast.WhileStatement)) {
	var walkStmt func(stmt ast.Statement)
	var walkExpr func(expr ast.Expression)

	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.WhileStatement:
			visit(s)
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.FunctionStatement:
			walkExpr(s.Body)
		case *ast.ExpressionStatement:
			walkExpr(s.Expression)
		case *ast.VariableDeclaration:
			if s.Value != nil {
				walkExpr(s.Value)
			}
		case *ast.AssignmentStatement:
			walkExpr(s.Value)
		}
	}
	walkExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, inner := range e.Block.Statements {
					walkStmt(inner)
				}
			}
		case *ast.MatchExpression:
			for _, arm := range e.Arms {
				walkExpr(arm.Body)
			}
		case *ast.FunctionLiteral:
			if e.Body != nil {
				for _, inner := range e.Body.Statements {
					walkStmt(inner)
				}
			}
		}
	}

	for _, stmt := range program.Statements {
		walkStmt(stmt)
	}
}

// countAssignments counts assignments to name anywhere under the block.
func countAssignments(block *ast.BlockStatement, name string) int {
	count := 0
	var walkStmt func(stmt ast.Statement)
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.AssignmentStatement:
			if s.Name != nil && s.Name.Value == name {
				count++
			}
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		}
	}
	if block != nil {
		for _, stmt := range block.Statements {
			walkStmt(stmt)
		}
	}
	return count
}

// findAssignment returns the first assignment to name under the block.
func findAssignment(block *ast.BlockStatement, name string) *ast.AssignmentStatement {
	var found *ast.AssignmentStatement
	var walkStmt func(stmt ast.Statement)
	walkStmt = func(stmt ast.Statement) {
		if found != nil {
			return
		}
		switch s := stmt.(type) {
		case *ast.AssignmentStatement:
			if s.Name != nil && s.Name.Value == name {
				found = s
			}
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		}
	}
	if block != nil {
		for _, stmt := range block.Statements {
			walkStmt(stmt)
		}
	}
	return found
}
