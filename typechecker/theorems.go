package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// Theorem declarations (docs/spec/125-verification.md). A theorem is a
// Bool-valued function whose parameters are universally quantified. The
// checker admits the shapes the discharge ladder can state: a monomorphic
// function of first-order parameters, no receiver, no variadic tail, no
// effect clauses, a body it types as Bool like any function body. What the
// body may compute is the extraction's and the deciders' concern; they
// fail closed on their own subsets.

// CodeTheoremShape reports a theorem declaration outside the statable
// shape.
const CodeTheoremShape = "OAK-V0001"

// checkTheoremShape reports the shape errors of a theorem and says whether
// the ordinary function check should continue.
func (tc *TypeChecker) checkTheoremShape(stmt *ast.FunctionStatement) bool {
	ok := true
	report := func(format string, args ...interface{}) {
		tc.addTypeDiagnostic(stmt.Name, CodeTheoremShape, fmt.Sprintf(format, args...))
		ok = false
	}
	if len(stmt.TypeParams) > 0 {
		report("theorem %s: a theorem is monomorphic; state it at the types it is about", stmt.Name.Value)
	}
	if stmt.Receiver != nil {
		report("theorem %s: a theorem has no receiver", stmt.Name.Value)
	}
	for _, param := range stmt.Parameters {
		if param.Variadic {
			report("theorem %s: a theorem quantifies over fixed parameters, not a variadic tail", stmt.Name.Value)
		}
	}
	if stmt.EffectsDeclared || stmt.Forbids != nil {
		report("theorem %s: a theorem is pure; it declares no effect clauses", stmt.Name.Value)
	}
	if stmt.ExternSymbol != "" {
		report("theorem %s: a theorem is stated in Oak, not bound to a foreign symbol", stmt.Name.Value)
	}
	return ok
}

// Theorems lists the theorem declarations of a checked program in source
// order.
func Theorems(program *ast.Program) []*ast.FunctionStatement {
	var out []*ast.FunctionStatement
	for _, stmt := range program.Statements {
		if fn, isFn := stmt.(*ast.FunctionStatement); isFn && fn.Theorem && fn.Name != nil {
			out = append(out, fn)
		}
	}
	return out
}
