package discipline

import (
	"fmt"

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
	forEachWhileInFunction(program, func(loop *ast.WhileStatement, function string) {
		if boundedWhileShape(loop) {
			return
		}
		// The title names the enclosing function and the rendered
		// diagnostic carries the loop's position, so a rejected loop is
		// found by reading, not by bisection (docs/spec/85-discipline.md
		// section 3; ml finding F8).
		title := "loop has no statically evident bound"
		if function != "" {
			title = fmt.Sprintf("loop in %s has no statically evident bound", function)
		}
		d := diagnostic.NewDiagnosticFromNodeWithCode(loop, "discipline", string(CodeUnboundedLoop), title)
		d.Severity = diagnostic.SeverityWarning
		d.SetPrimary(diagnostic.NodeToRange(loop), describeLoopShape(loop))
		d.AddNote("the strict profile requires every loop to have a statically evident bound (docs/spec/85-discipline.md section 3)")
		d.AddHelp("use the canonical bounded shape — while i < bound with exactly one `i = i + k` step (k a positive constant: a literal or T(literal)) and an unmodified bound — or restructure into bounded tail recursion")
		r.diagnostics = append(r.diagnostics, d)
	})
}

// describeLoopShape explains which part of the canonical shape a loop
// misses, in programmer terms (docs/spec/15-diagnostics.md section 4).
func describeLoopShape(loop *ast.WhileStatement) string {
	condition, ok := loop.Condition.(*ast.InfixExpression)
	if !ok || (condition.Operator != "<" && condition.Operator != "<=") {
		return "the condition is not `counter < bound` or `counter <= bound`"
	}
	counter, ok := condition.Left.(*ast.Identifier)
	if !ok {
		return "the left side of the condition is not a counter variable"
	}
	switch bound := condition.Right.(type) {
	case *ast.Identifier:
		if bound.Value == counter.Value {
			return "the bound is the counter itself"
		}
		if countAssignments(loop.Body, bound.Value) != 0 {
			return fmt.Sprintf("the bound %s is reassigned inside the loop body", bound.Value)
		}
	default:
		if !isIntegerConstant(condition.Right) {
			return "the bound is neither a constant nor an unmodified variable"
		}
	}
	switch n := countAssignments(loop.Body, counter.Value); {
	case n == 0:
		return fmt.Sprintf("the counter %s is never advanced in the loop body", counter.Value)
	case n > 1:
		return fmt.Sprintf("the counter %s is assigned %d times in the loop body; the canonical shape assigns it exactly once", counter.Value, n)
	}
	return fmt.Sprintf("the step is not `%s = %s + k` with k a positive constant", counter.Value, counter.Value)
}

// integerTypeNames are the constructor names accepted in a constant step or
// bound: `u32(1)` is the same constant as `1` (docs/spec/25-type-inference.md
// section 3a), and the discipline analysis runs before literal typing
// would fold it, so the shape check recognizes the constructor itself.
var integerTypeNames = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true,
	"i8": true, "i16": true, "i32": true, "i64": true,
	"int": true, "uint": true, "uptr": true, "byte": true, "rune": true,
}

// integerConstant extracts the value of an integer constant expression: an
// integer literal, or an integer-type constructor applied to exactly one
// integer literal (`u32(1)`, `i64(8)`).
func integerConstant(expr ast.Expression) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.InvocationExpression:
		name, ok := e.Function.(*ast.Identifier)
		if !ok || !integerTypeNames[name.Value] || len(e.Arguments) != 1 {
			return 0, false
		}
		literal, ok := e.Arguments[0].(*ast.IntegerLiteral)
		if !ok {
			return 0, false
		}
		return literal.Value, true
	}
	return 0, false
}

func isIntegerConstant(expr ast.Expression) bool {
	_, ok := integerConstant(expr)
	return ok
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

	// The bound must be fixed: an integer constant (a literal or
	// `T(literal)`), or an identifier the body never reassigns.
	switch bound := condition.Right.(type) {
	case *ast.Identifier:
		if bound.Value == counter.Value || countAssignments(loop.Body, bound.Value) != 0 {
			return false
		}
	default:
		if !isIntegerConstant(condition.Right) {
			return false
		}
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
	step, ok := integerConstant(sum.Right)
	return ok && step >= 1
}

// forEachWhile visits every while statement in the program, including those
// nested in function bodies, blocks, unsafe blocks, and expression blocks.
func forEachWhile(program *ast.Program, visit func(*ast.WhileStatement)) {
	forEachWhileInFunction(program, func(loop *ast.WhileStatement, _ string) { visit(loop) })
}

// forEachWhileInFunction is forEachWhile with the name of the enclosing
// top-level function ("" for a loop outside any function) passed along.
func forEachWhileInFunction(program *ast.Program, visit func(*ast.WhileStatement, string)) {
	var walkStmt func(stmt ast.Statement)
	var walkExpr func(expr ast.Expression)
	function := ""

	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.WhileStatement:
			visit(s, function)
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.IfStatement:
			if s.Consequence != nil {
				for _, inner := range s.Consequence.Statements {
					walkStmt(inner)
				}
			}
			if s.Alternative != nil {
				walkStmt(s.Alternative)
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
			enclosing := function
			if s.Name != nil {
				function = s.Name.Value
			}
			walkExpr(s.Body)
			function = enclosing
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
		case *ast.IfStatement:
			if s.Consequence != nil {
				for _, inner := range s.Consequence.Statements {
					walkStmt(inner)
				}
			}
			if s.Alternative != nil {
				walkStmt(s.Alternative)
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
		case *ast.IfStatement:
			if s.Consequence != nil {
				for _, inner := range s.Consequence.Statements {
					walkStmt(inner)
				}
			}
			if s.Alternative != nil {
				walkStmt(s.Alternative)
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
