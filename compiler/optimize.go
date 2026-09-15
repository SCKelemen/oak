package compiler

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/typechecker"
)

// Compiler-facing aliases keep the report near SemanticModel while the
// planning vocabulary and fail-closed candidate search live in opt/.
type OptimizationRule = string
type OptimizationDecision = opt.Remark
type OptimizationReport = opt.Report

const (
	// OptimizationInlineLeaf beta-reduces a syntactically safe private leaf
	// helper so caller facts reach the helper's indexed accesses.
	OptimizationInlineLeaf OptimizationRule = "source.inline.leaf.v1"
	// OptimizationCanonicalBool removes redundant built-in Bool operators
	// after generic specialization without deleting non-literal operands.
	OptimizationCanonicalBool OptimizationRule = "source.canonical.bool.v1"
	// OptimizationCanonicalInteger removes fixed-width zero/one identity
	// operators after specialization without deleting non-literal operands.
	OptimizationCanonicalInteger OptimizationRule = "source.canonical.integer.v1"
)

// optimizeBeforeSpecialization runs cheap source transforms before generic
// elaboration. The resulting tree is subsequently typechecked like any other
// program.
func optimizeBeforeSpecialization(program *ast.Program, protocols []*ast.ProtocolDeclaration) OptimizationReport {
	return optimizationReport(inlineHelpers(program, protocols))
}

// optimizeAfterSpecialization runs transforms that benefit from concrete
// generic bodies and checked operand facts. The caller re-typechecks every
// changed program before a backend may consume it.
func optimizeAfterSpecialization(program *ast.Program, tc *typechecker.TypeChecker) OptimizationReport {
	decisions := canonicalizeBooleans(program, tc)
	decisions = append(decisions, canonicalizeIntegers(program, tc)...)
	return optimizationReport(decisions)
}

// addPostSpecializationValidationTypes supplies the independent checker with
// concrete declarations that the specializing checker recorded but did not
// append to the emitted AST. Compiler normalization may expose their mangled
// names (notably in closure captures). The declarations exist only in the
// validation clone and come solely from the first checker's instantiation set.
func addPostSpecializationValidationTypes(program *ast.Program, tc *typechecker.TypeChecker) {
	if program == nil || tc == nil {
		return
	}
	templates := map[string]*ast.ADTType{}
	existing := map[string]bool{}
	for _, statement := range program.Statements {
		declaration, isADT := statement.(*ast.ADTType)
		if !isADT || declaration.Name == nil {
			continue
		}
		existing[declaration.Name.Value] = true
		if len(declaration.TypeParams) > 0 {
			templates[declaration.Name.Value] = declaration
		}
	}
	for _, declaration := range specializedInstantiationDeclarations(tc, templates) {
		if declaration.Name == nil || existing[declaration.Name.Value] {
			continue
		}
		existing[declaration.Name.Value] = true
		program.Statements = append(program.Statements, declaration)
	}
}

// specializedInstantiationDeclarations is the single construction path for
// concrete generic ADTs needed by native lowering and by the independent
// post-specialization validation clone. Its input is restricted to
// instantiations recorded by the specializing typechecker.
func specializedInstantiationDeclarations(tc *typechecker.TypeChecker, templates map[string]*ast.ADTType) []*ast.ADTType {
	if tc == nil {
		return nil
	}
	var declarations []*ast.ADTType
	for _, instantiation := range tc.ADTInstantiations() {
		template, declared := templates[instantiation.ADT]
		if !declared || len(template.TypeParams) != len(instantiation.Args) {
			continue
		}
		bindings := make(map[string]ast.Expression, len(instantiation.Args))
		for i, parameter := range template.TypeParams {
			if parameter != nil && parameter.Name != nil {
				bindings[parameter.Name.Value] = argumentExpressionOf(instantiation.Args[i])
			}
		}
		specialized := &ast.ADTType{
			BaseNode:  template.BaseNode,
			Token:     template.Token,
			EndToken:  template.EndToken,
			Name:      &ast.Identifier{Token: template.Name.Token, Value: instantiation.MangledName()},
			TagValues: template.TagValues,
		}
		valid := true
		for _, variant := range template.Variants {
			payload, ok := typechecker.SubstituteTypeAST(variant.Payload, bindings)
			if !ok {
				valid = false
				break
			}
			literal := variant.Literal
			if record, isRecord := variant.Literal.(*ast.RecordLiteral); isRecord {
				substituted := &ast.RecordLiteral{
					BaseNode: record.BaseNode,
					Token:    record.Token,
					EndToken: record.EndToken,
					Fields:   map[string]ast.Expression{},
					Layout:   record.Layout,
					TypeName: record.TypeName,
				}
				for _, field := range record.FieldOrder {
					fieldType, ok := typechecker.SubstituteTypeAST(field.Value, bindings)
					if !ok {
						valid = false
						break
					}
					substituted.Fields[field.Name] = fieldType
					substituted.FieldOrder = append(substituted.FieldOrder, ast.RecordField{Token: field.Token, Name: field.Name, Value: fieldType, Align: field.Align})
				}
				if !valid {
					break
				}
				literal = substituted
			}
			specialized.Variants = append(specialized.Variants, &ast.ADTVariant{
				Token:   variant.Token,
				Name:    variant.Name,
				Payload: payload,
				Literal: literal,
				Result:  variant.Result,
			})
		}
		if valid {
			declarations = append(declarations, specialized)
		}
	}
	return declarations
}

func optimizationReport(decisions []OptimizationDecision) OptimizationReport {
	return OptimizationReport{Remarks: append([]OptimizationDecision(nil), decisions...)}
}

func mergeOptimizationReports(reports ...OptimizationReport) OptimizationReport {
	var merged OptimizationReport
	for _, report := range reports {
		merged.Remarks = append(merged.Remarks, report.Remarks...)
	}
	return merged
}

// Optimizations checks the executable-oriented program and returns the
// transformations it applied. Native rules are included when NativeBodies is
// enabled on the compilation. The returned report cannot alter compilation.
func (comp Compilation) Optimizations() Stage[OptimizationReport] {
	comp.options.InlineHelpers = true
	return comp.Check().Map(func(model *SemanticModel) OptimizationReport {
		return optimizationReport(model.Optimizations.Remarks)
	})
}
