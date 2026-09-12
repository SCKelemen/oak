package prove

import (
	"fmt"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
)

// ProblemFor serializes the named theorem for the Oak solver
// (prove/solver/bdd.oak) under the variable order that decided it and the
// node budget given: the same lowering the bit-level decider ran, so the
// Oak solver replays the decision and the two are compared on the verdict
// and the node count. The reason names what keeps the theorem from the
// bit level.
func ProblemFor(model *compiler.SemanticModel, name, order string, budget int) (asm.Problem, string, error) {
	if model == nil || model.Tree == nil || model.Tree.Root == nil || model.TypeChecker == nil {
		return asm.Problem{}, "", fmt.Errorf("prove: no checked program")
	}
	functions := map[string]*ast.FunctionStatement{}
	var theorem *ast.FunctionStatement
	for _, stmt := range model.Tree.Root.Statements {
		fn, isFn := stmt.(*ast.FunctionStatement)
		if !isFn || fn.Name == nil {
			continue
		}
		functions[fn.Name.Value] = fn
		if fn.Theorem && fn.Name.Value == name {
			theorem = fn
		}
	}
	if theorem == nil {
		return asm.Problem{}, "", fmt.Errorf("prove: no theorem %s", name)
	}
	stated, callees, guards, reason := forDecider(model.TypeChecker, theorem, functions)
	if reason != "" {
		return asm.Problem{}, reason, nil
	}
	problem, reason, ok := asm.ExportProblem(stated, callees, guards, declarationsOf(model.Tree.Root), order, budget)
	if !ok {
		return asm.Problem{}, reason, nil
	}
	return problem, "", nil
}
