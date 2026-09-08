package typechecker

// Representation specialization for extensible-record functions.
//
// A parameter such as { r | name: string } is a structural constraint, not
// a C layout. The source declaration is therefore treated as a template.
// Each open parameter is replaced privately with a synthetic type parameter;
// the existing generic-function monomorphizer then clones and fully checks one
// ordinary function for every concrete struct combination used by the program.
// Downstream stages never see an open-row ABI.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

func hasOpenRowParameters(fn *ast.FunctionStatement) bool {
	if fn == nil {
		return false
	}
	for _, parameter := range fn.Parameters {
		if record, ok := parameter.Type.(*ast.RecordLiteral); ok && record.Extension != nil {
			return true
		}
	}
	return false
}

func (tc *TypeChecker) registerRowFunctionTemplate(fn *ast.FunctionStatement) {
	if fn == nil || fn.Name == nil {
		return
	}
	if tc.rowFunctionTemplates == nil {
		tc.rowFunctionTemplates = make(map[string]bool)
	}
	if tc.rowFunctionTemplates[fn.Name.Value] {
		return
	}

	template := *fn
	template.Parameters = make([]*ast.FunctionParameter, 0, len(fn.Parameters))
	template.TypeParams = append([]*ast.TypeParameter(nil), fn.TypeParams...)
	requirements := make(map[string]*RecordType)

	for i, parameter := range fn.Parameters {
		clone := *parameter
		recordExpr, open := parameter.Type.(*ast.RecordLiteral)
		if !open || recordExpr.Extension == nil {
			template.Parameters = append(template.Parameters, &clone)
			continue
		}
		requirement, ok := tc.parseTypeExpression(recordExpr).(*RecordType)
		if !ok || !requirement.Open {
			tc.addError(parameter.Type, "invalid extensible-record parameter")
			return
		}
		synthetic := fmt.Sprintf("__oak_row_%d", i)
		identifier := &ast.Identifier{Token: parameter.Token, Value: synthetic}
		clone.Type = identifier
		template.Parameters = append(template.Parameters, &clone)
		template.TypeParams = append(template.TypeParams, &ast.TypeParameter{
			Token: parameter.Token,
			Name:  identifier,
		})
		requirements[synthetic] = requirement
	}

	if tc.functionTemplates == nil {
		tc.functionTemplates = make(map[string]*ast.FunctionStatement)
	}
	if tc.functionTemplateRowRequirements == nil {
		tc.functionTemplateRowRequirements = make(map[string]map[string]*RecordType)
	}
	tc.functionTemplates[fn.Name.Value] = &template
	tc.functionTemplateRowRequirements[fn.Name.Value] = requirements
	tc.rowFunctionTemplates[fn.Name.Value] = true
}

func (tc *TypeChecker) validateTemplateRowArguments(at ast.Node, template *ast.FunctionStatement, args []Type) bool {
	if template == nil || template.Name == nil {
		return false
	}
	requirements := tc.functionTemplateRowRequirements[template.Name.Value]
	if len(requirements) == 0 {
		return true
	}
	for i, parameter := range template.TypeParams {
		requirement, constrained := requirements[parameter.Name.Value]
		if !constrained {
			continue
		}
		if i >= len(args) || !tc.isAssignable(args[i], requirement) {
			actual := "<missing>"
			if i < len(args) && args[i] != nil {
				actual = args[i].String()
			}
			tc.addError(at, "argument type %s does not satisfy extensible record constraint %s", actual, requirement)
			return false
		}
	}
	return true
}
