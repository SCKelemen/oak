package typechecker

import (
	"fmt"
	"reflect"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Generic refinements (docs/spec/20-types.md section 12.1):
//
//	IrqId[N: u32]: type = u16 where value < N
//
// A refinement whose type parameters are integer constants is a template
// over the predicate. It is specialized before checking, the way region
// parameters are erased (typechecker/regions.go) and generic functions are
// monomorphized (typechecker/genericfn.go): every application `IrqId[4]`
// in the program — a parameter type, a binding's type, a construction
// `IrqId[4](v)` — is rewritten to the mangled name `IrqId_4`, and the
// template statement is replaced by one ordinary refinement declaration
// per distinct instantiation, its predicate with the literal substituted
// (`value < 4`). The checker, the extent facts and their discharge, the C
// backend's guard, the Lean projection, the interpreter, and the prover
// then see only plain refinements; nothing downstream knows templates
// exist. The arguments are literals: the const parameter of an enclosing
// template is not yet a valid argument.

// refinementTemplateSet is the state of one specialization pass.
type refinementTemplateSet struct {
	templates map[string]*ast.ADTType   // name -> template (nil when the declaration was rejected)
	instances map[string][]*ast.ADTType // template name -> specializations, in first-use order
	seen      map[string]bool           // mangled names already specialized
	// live marks the set after the initial pass: an application found
	// later — a record template's substituted field, a generic
	// function's specialized clone — is specialized on demand, registered
	// at once, and its declaration appended to the program at the end of
	// checking (late).
	live bool
	late []ast.Statement
}

// specializeRefinementTemplates rewrites every application of a generic
// refinement in the program and replaces the templates by their
// instantiations.
func (tc *TypeChecker) specializeRefinementTemplates(program *ast.Program) {
	set := &refinementTemplateSet{
		templates: map[string]*ast.ADTType{},
		instances: map[string][]*ast.ADTType{},
		seen:      map[string]bool{},
	}
	for _, stmt := range program.Statements {
		adt, isADT := stmt.(*ast.ADTType)
		if !isADT || adt.Refinement == nil || len(adt.TypeParams) == 0 || adt.Name == nil {
			continue
		}
		set.templates[adt.Name.Value] = adt
		for _, param := range adt.TypeParams {
			if param == nil || param.Name == nil || !isConstParameter(param) {
				tc.addTypeDiagnostic(adt.Name, CodeRefinementShape,
					fmt.Sprintf("refinement %s: a generic refinement's parameters are integer constants (N: u32), not types", adt.Name.Value))
				set.templates[adt.Name.Value] = nil
				break
			}
		}
		if len(adt.Variants) != 1 || adt.Variants[0].Payload == nil {
			tc.addTypeDiagnostic(adt.Name, CodeRefinementShape,
				fmt.Sprintf("refinement %s: a refinement names one base type", adt.Name.Value))
			set.templates[adt.Name.Value] = nil
		}
	}
	if len(set.templates) == 0 {
		return
	}
	tc.refinementTemplateSet = set
	tc.rewriteRefinementApplications(reflect.ValueOf(program), set)
	kept := make([]ast.Statement, 0, len(program.Statements))
	for _, stmt := range program.Statements {
		if adt, isADT := stmt.(*ast.ADTType); isADT && adt.Name != nil {
			if _, isTemplate := set.templates[adt.Name.Value]; isTemplate {
				for _, instance := range set.instances[adt.Name.Value] {
					kept = append(kept, instance)
				}
				continue
			}
		}
		kept = append(kept, stmt)
	}
	program.Statements = kept
	set.live = true
	tc.noteRefinementInstances(set)
}

// noteRefinementInstances records every specialization for `oak vet`.
func (tc *TypeChecker) noteRefinementInstances(set *refinementTemplateSet) {
	tc.refinementTemplates = map[string][]string{}
	for name, instances := range set.instances {
		for _, instance := range instances {
			tc.refinementTemplates[name] = append(tc.refinementTemplates[name], instance.Name.Value)
		}
	}
}

// appendLateRefinementInstances adds the specializations created after
// the initial pass to the program, so the backends and the interpreter
// see their declarations.
func (tc *TypeChecker) appendLateRefinementInstances(program *ast.Program) {
	set := tc.refinementTemplateSet
	if set == nil || len(set.late) == 0 {
		return
	}
	program.Statements = append(program.Statements, set.late...)
	set.late = nil
	tc.noteRefinementInstances(set)
}

// refinementTemplateApplication resolves a type expression that applies a
// generic refinement to literal arguments, specializing on demand; nil
// when the expression is anything else.
func (tc *TypeChecker) refinementTemplateApplication(expr ast.Expression) *ast.Identifier {
	set := tc.refinementTemplateSet
	index, isIndex := expr.(*ast.IndexExpression)
	if set == nil || !isIndex || index.Dot {
		return nil
	}
	if replacement, isIdent := tc.refinementApplication(index, set).(*ast.Identifier); isIdent {
		return replacement
	}
	return nil
}

// RefinementApplicationName reports the specialization an application of
// a generic refinement to literal arguments names, when it exists; a
// lookup for the backends, which never creates one.
func (tc *TypeChecker) RefinementApplicationName(expr ast.Expression) (string, bool) {
	set := tc.refinementTemplateSet
	index, isIndex := expr.(*ast.IndexExpression)
	if set == nil || !isIndex || index.Dot {
		return "", false
	}
	name, args, ok := lenientFlattenApplication(index)
	if !ok || len(args) == 0 {
		return "", false
	}
	template, isTemplate := set.templates[name]
	if !isTemplate || template == nil || len(args) != len(template.TypeParams) {
		return "", false
	}
	atoms := make([]string, 0, len(args))
	for _, arg := range args {
		literal, isLiteral := arg.(*ast.IntegerLiteral)
		if !isLiteral {
			return "", false
		}
		atoms = append(atoms, strconv.FormatInt(literal.Value, 10))
	}
	mangled := Instantiation{ADT: name, Args: atoms}.MangledName()
	return mangled, set.seen[mangled]
}

// rewriteRefinementApplications walks every node reachable from value and
// replaces each template application in a settable position by the
// identifier of its specialization. Record literals keep their field map
// and field order in step.
func (tc *TypeChecker) rewriteRefinementApplications(value reflect.Value, set *refinementTemplateSet) {
	switch value.Kind() {
	case reflect.Ptr, reflect.Interface:
		if value.IsNil() {
			return
		}
		if value.CanInterface() {
			switch node := value.Interface().(type) {
			case *ast.IndexExpression:
				if replacement := tc.refinementApplication(node, set); replacement != nil {
					if value.CanSet() && reflect.TypeOf(replacement).AssignableTo(value.Type()) {
						value.Set(reflect.ValueOf(replacement))
					}
					return
				}
			case *ast.RecordLiteral:
				for i := range node.FieldOrder {
					application, isIndex := node.FieldOrder[i].Value.(*ast.IndexExpression)
					if !isIndex {
						continue
					}
					if replacement := tc.refinementApplication(application, set); replacement != nil {
						node.FieldOrder[i].Value = replacement
						node.Fields[node.FieldOrder[i].Name] = replacement
					}
				}
			}
		}
		tc.rewriteRefinementApplications(value.Elem(), set)
	case reflect.Struct:
		if value.Type() == reflect.TypeOf(token.Token{}) {
			return
		}
		for i := 0; i < value.NumField(); i++ {
			field := value.Field(i)
			if field.CanSet() || field.Kind() == reflect.Ptr || field.Kind() == reflect.Interface || field.Kind() == reflect.Slice {
				tc.rewriteRefinementApplications(field, set)
			}
		}
	case reflect.Slice:
		for i := 0; i < value.Len(); i++ {
			tc.rewriteRefinementApplications(value.Index(i), set)
		}
	case reflect.Map:
		for _, key := range value.MapKeys() {
			tc.rewriteRefinementApplications(value.MapIndex(key), set)
		}
	}
}

// refinementApplication specializes one application `Name[k...]` of a
// generic refinement and returns the identifier that replaces it; nil when
// the node is not an application of a template (array syntax, another
// name) or when the arguments are not acceptable constants (diagnosed).
func (tc *TypeChecker) refinementApplication(node *ast.IndexExpression, set *refinementTemplateSet) ast.Expression {
	name, args, ok := lenientFlattenApplication(node)
	if !ok || len(args) == 0 {
		return nil
	}
	template, isTemplate := set.templates[name]
	if !isTemplate {
		return nil
	}
	if template == nil {
		return nil // the declaration was rejected; one diagnostic is enough
	}
	if len(args) > len(template.TypeParams) {
		// `[4]IrqId[4]` flattens to two arguments: the array (or arrays)
		// of an application. The application sits at the depth of the
		// extra indices; it is rewritten in place and the outer nodes stay
		// array syntax.
		parent := node
		for depth := len(args) - len(template.TypeParams); depth > 1; depth-- {
			next, isIndex := parent.Left.(*ast.IndexExpression)
			if !isIndex {
				return nil
			}
			parent = next
		}
		if application, isIndex := parent.Left.(*ast.IndexExpression); isIndex {
			if replacement := tc.refinementApplication(application, set); replacement != nil {
				parent.Left = replacement
			}
		}
		return nil
	}
	if len(args) < len(template.TypeParams) {
		tc.addTypeDiagnostic(node, CodeRefinementShape,
			fmt.Sprintf("refinement %s takes %d constant argument(s), got %d", name, len(template.TypeParams), len(args)))
		return nil
	}
	bindings := make(map[string]ast.Expression, len(args))
	atoms := make([]string, 0, len(args))
	for i, arg := range args {
		param := template.TypeParams[i]
		literal, isLiteral := arg.(*ast.IntegerLiteral)
		if !isLiteral {
			if _, isIdent := arg.(*ast.Identifier); isIdent {
				// A name in argument position: possibly a const parameter
				// of an enclosing template, which this pass does not yet
				// resolve. Left to the checker.
				return nil
			}
			tc.addTypeDiagnostic(node, CodeRefinementShape,
				fmt.Sprintf("refinement %s: argument %s for %s must be an integer literal", name, arg.String(), param.Name.Value))
			return nil
		}
		kind := constParameterKind(param)
		if literal.Wide || literal.Value < 0 || !tc.literalFitsInType(literal.Value, kind) {
			tc.addTypeDiagnostic(node, CodeRefinementShape,
				fmt.Sprintf("refinement %s: literal %s does not fit in type %s (const parameter %s)", name, literal.String(), kind, param.Name.Value))
			return nil
		}
		digits := strconv.FormatInt(literal.Value, 10)
		atoms = append(atoms, digits)
		bindings[param.Name.Value] = &ast.IntegerLiteral{Token: token.Token{TokenKind: token.INT, Literal: digits}, Value: literal.Value}
	}
	mangled := Instantiation{ADT: name, Args: atoms}.MangledName()
	if !set.seen[mangled] {
		predicate, okSubst := substituteExpr(template.Refinement, bindings)
		if !okSubst {
			tc.addTypeDiagnostic(template.Refinement, CodeRefinementShape,
				fmt.Sprintf("refinement %s: the predicate is outside the shape a generic refinement can specialize", name))
			return nil
		}
		base := template.Variants[0]
		specialized := &ast.ADTType{
			Token:    template.Token,
			EndToken: template.EndToken,
			Name:     &ast.Identifier{Token: template.Name.Token, Value: mangled},
			Variants: []*ast.ADTVariant{{
				Token:   base.Token,
				Name:    &ast.Identifier{Token: template.Name.Token, Value: mangled},
				Payload: base.Payload,
			}},
			Refinement: predicate,
			Exported:   template.Exported,
			Opaque:     template.Opaque,
		}
		set.seen[mangled] = true
		set.instances[name] = append(set.instances[name], specialized)
		if set.live {
			// Found after the initial pass: register the declaration now,
			// under the global scope, and append it to the program later.
			outer := tc.env
			if tc.globalEnv != nil {
				tc.env = tc.globalEnv
			}
			tc.checkRefinementType(specialized)
			tc.env = outer
			set.late = append(set.late, specialized)
		}
	}
	return &ast.Identifier{Token: node.Token, Value: mangled}
}

// RefinementTemplates reports each generic refinement with the names of
// its specializations, in first-use order (for `oak vet`).
func (tc *TypeChecker) RefinementTemplates() map[string][]string {
	return tc.refinementTemplates
}
