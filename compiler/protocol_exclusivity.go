package compiler

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// ExclusivityMarker is the infix of a generated guard-exclusivity theorem's
// name: `<prefix>__exclusive__<Protocol>__<step>__<From>__<i>__<j>`. The
// fields are joined by double underscores, which no identifier contains
// (reserved for internal names), so the row that folds the pairs can
// spell the declaration's own names.
const ExclusivityMarker = "__exclusive__"

// ProtocolGuardExclusivity synthesizes, for every protocol of a lowered
// tree and every (step, source state) group with two or more guarded lines,
// one theorem per pair of lines stating that their guards never hold
// together (docs/spec/112-protocols.md section 1): Oak takes the first
// line whose guard holds and the model checker explores every line whose
// guard holds, and the two readings coincide exactly when the guards are
// pairwise disjoint. The theorems quantify over the data record and the
// step's payload, the guards' `data` renamed to the parameter and their
// quantifier forms rewritten to the projected helpers, and the prover
// decides them like any other theorem.
func ProtocolGuardExclusivity(tree *SyntaxTree) []ast.Statement {
	var out []ast.Statement
	decls := ProtocolDeclarationsOf(tree.Root)
	for _, decl := range Protocols(tree) {
		if decl == nil || decl.Name == nil {
			continue
		}
		machine, ok := analyzeProtocolDecls(decl, decls, func(string, ast.Node, string, ...interface{}) {})
		if !ok {
			continue
		}
		prefix := snakeCase(machine.name)
		s := newSynth(helperContext(decl.Name.Token.SemanticContext, machine.name+"Exclusive"))
		for _, step := range machine.steps {
			groups := map[string][]*ast.ProtocolTransition{}
			var sources []string
			for _, line := range step.lines {
				if line.Guard == nil {
					continue
				}
				from := line.From.Value
				if _, seen := groups[from]; !seen {
					sources = append(sources, from)
				}
				groups[from] = append(groups[from], line)
			}
			for _, from := range sources {
				lines := groups[from]
				if len(lines) < 2 {
					continue
				}
				for i := 0; i < len(lines); i++ {
					for j := i + 1; j < len(lines); j++ {
						name := fmt.Sprintf("%s%s%s__%s__%s__%d__%d", prefix, ExclusivityMarker, machine.name, step.name, from, i, j)
						var params []*ast.FunctionParameter
						if decl.Data != nil {
							params = append(params, s.param("oak_d", s.id(machine.name+"Data")))
						}
						if step.payload != nil {
							params = append(params, s.param(step.payload.Name.Value, cloneExpression(step.payload.Type)))
						}
						guard := func(line *ast.ProtocolTransition) ast.Expression {
							stmt := &ast.ExpressionStatement{Expression: machine.lineGuard(s, line)}
							machine.rewriteQuantifiers(stmt, prefix, s)
							return renameIdentifier(stmt.Expression, "data", "oak_d").(ast.Expression)
						}
						body := s.not(s.and(guard(lines[i]), guard(lines[j])))
						fn := s.fnExpr(name, params, s.id("Bool"), body)
						fn.Theorem = true
						out = append(out, fn)
					}
				}
			}
		}
	}
	return out
}
