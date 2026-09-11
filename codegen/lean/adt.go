package lean

// Sum types, variant matches, generic instantiations, and hoisted
// conditionals (docs/spec/95-extraction.md section 2, the standard-library
// round). Every Oak ADT the extracted functions mention becomes a Lean
// `inductive` (records stay `structure`s); a generic ADT is extracted per
// recorded instantiation under the type checker's mangled name, exactly the
// concrete tagged union the C backend emits (codegen/mono.go), so
// `Result[u32, VarintError]` is `Result_u32_VarintError`. Variant
// construction is the constructor application, a match over variants is a
// Lean `match`, and a value-position conditional whose arms carry
// statements or calls is bound through a do-block so nothing in an untaken
// arm is evaluated.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// isRecordADT reports whether an ADT declaration is a record (one variant
// whose literal is a field list).
func isRecordADT(adt *ast.ADTType) bool {
	if len(adt.Variants) != 1 || adt.Variants[0].Literal == nil {
		return false
	}
	_, ok := adt.Variants[0].Literal.(*ast.RecordLiteral)
	return ok
}

// collectTypes registers every ADT declaration of the program and every
// recorded generic instantiation, specialized the way the C backend
// specializes it. Templates themselves are never emitted.
func (em *emitter) collectTypes(program *ast.Program) {
	for _, stmt := range program.Statements {
		adt, ok := stmt.(*ast.ADTType)
		if !ok || adt.Name == nil {
			continue
		}
		em.adts[adt.Name.Value] = adt
		em.typeOrder = append(em.typeOrder, adt.Name.Value)
	}
	for _, inst := range em.tc.ADTInstantiations() {
		template, known := em.adts[inst.ADT]
		if !known || len(template.TypeParams) == 0 {
			continue
		}
		mangled := inst.MangledName()
		if _, exists := em.adts[mangled]; exists {
			continue
		}
		if specialized, ok := specializeADT(template, inst); ok {
			em.adts[mangled] = specialized
			em.typeOrder = append(em.typeOrder, mangled)
		}
	}
	for name, adt := range em.adts {
		if len(adt.TypeParams) == 0 && isRecordADT(adt) {
			em.records[name] = adt
		}
	}
}

// specializeADT substitutes an instantiation's argument atoms into the
// template's variant payloads and record fields (typechecker.SubstituteTypeAST
// is the single substitution authority, as in codegen/mono.go).
func specializeADT(template *ast.ADTType, inst typechecker.Instantiation) (*ast.ADTType, bool) {
	if len(template.TypeParams) != len(inst.Args) {
		return nil, false
	}
	bindings := make(map[string]ast.Expression, len(inst.Args))
	for i, param := range template.TypeParams {
		if param == nil || param.Name == nil {
			return nil, false
		}
		bindings[param.Name.Value] = atomExpression(inst.Args[i])
	}
	specialized := &ast.ADTType{
		BaseNode: template.BaseNode,
		Token:    template.Token,
		EndToken: template.EndToken,
		Name:     &ast.Identifier{Token: template.Name.Token, Value: inst.MangledName()},
	}
	for _, variant := range template.Variants {
		payload, ok := typechecker.SubstituteTypeAST(variant.Payload, bindings)
		if !ok {
			return nil, false
		}
		literal := variant.Literal
		if recordLit, isRecord := variant.Literal.(*ast.RecordLiteral); isRecord {
			substituted := &ast.RecordLiteral{
				BaseNode: recordLit.BaseNode,
				Token:    recordLit.Token,
				EndToken: recordLit.EndToken,
				Fields:   make(map[string]ast.Expression, len(recordLit.Fields)),
				Layout:   recordLit.Layout,
			}
			for _, field := range recordLit.FieldOrder {
				value, okField := typechecker.SubstituteTypeAST(field.Value, bindings)
				if !okField {
					return nil, false
				}
				substituted.Fields[field.Name] = value
				substituted.FieldOrder = append(substituted.FieldOrder, ast.RecordField{
					Token: field.Token, Name: field.Name, Value: value, Align: field.Align,
				})
			}
			literal = substituted
		}
		specialized.Variants = append(specialized.Variants, &ast.ADTVariant{
			Token: variant.Token, Name: variant.Name, Payload: payload, Literal: literal,
		})
	}
	return specialized, true
}

// atomExpression renders a mangled argument atom back to type syntax.
func atomExpression(atom string) ast.Expression {
	numeric := atom != ""
	for i := 0; i < len(atom); i++ {
		if atom[i] < '0' || atom[i] > '9' {
			numeric = false
			break
		}
	}
	if numeric {
		var value int64
		for i := 0; i < len(atom); i++ {
			value = value*10 + int64(atom[i]-'0')
		}
		return &ast.IntegerLiteral{Value: value}
	}
	return &ast.Identifier{Value: atom}
}

// applicationName resolves a type expression that applies a generic ADT
// template (Result[u32, VarintError], Option[u8]) to its mangled
// instantiation name. Array syntax ([4]u8, []u8, [*]u8) is not an
// application: the template registry disambiguates, as in the checker.
func (em *emitter) applicationName(expr ast.Expression) (string, bool) {
	name, args, ok := flattenApplication(expr)
	if !ok || len(args) == 0 {
		return "", false
	}
	template, declared := em.adts[name]
	if !declared || len(template.TypeParams) != len(args) {
		return "", false
	}
	atoms := make([]string, 0, len(args))
	for _, arg := range args {
		atom, okAtom := em.atomOf(arg)
		if !okAtom {
			return "", false
		}
		atoms = append(atoms, atom)
	}
	return typechecker.Instantiation{ADT: name, Args: atoms}.MangledName(), true
}

func flattenApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, nil, e.Value != ""
	case *ast.IndexExpression:
		if e.Dot || e.Index == nil {
			return "", nil, false
		}
		if marker, isIdent := e.Index.(*ast.Identifier); isIdent && (marker.Value == "" || marker.Value == "*") {
			return "", nil, false
		}
		name, args, ok := flattenApplication(e.Left)
		if !ok {
			return "", nil, false
		}
		return name, append(args, e.Index), true
	}
	return "", nil, false
}

// atomOf is the mangled spelling of one type argument.
func (em *emitter) atomOf(expr ast.Expression) (string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if _, isPrimitive := primitiveLean[e.Value]; isPrimitive {
			return e.Value, true
		}
		return normalizePrimitive(e.Value), e.Value != ""
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", e.Value), true
	case *ast.IndexExpression:
		return em.applicationName(e)
	}
	return "", false
}

// atomOfType is the mangled spelling of a checked type argument.
func atomOfType(typ typechecker.Type) (string, bool) {
	switch t := typ.(type) {
	case *typechecker.PrimitiveType:
		return normalizePrimitive(t.Name), true
	case *typechecker.BoolType:
		return "Bool", true
	case *typechecker.ADTType:
		return t.Name, true
	case *typechecker.RecordType:
		if t.Name != "" {
			return t.Name, true
		}
	case *typechecker.ConstIntType:
		return fmt.Sprintf("%d", t.Value), true
	case *typechecker.GenericType:
		atoms := make([]string, 0, len(t.TypeArgs))
		for _, arg := range t.TypeArgs {
			atom, ok := atomOfType(arg)
			if !ok {
				return "", false
			}
			atoms = append(atoms, atom)
		}
		return typechecker.Instantiation{ADT: t.Name, Args: atoms}.MangledName(), true
	}
	return "", false
}

// adtLeanName renders a known, non-template ADT as its Lean type name and
// marks it for emission.
func (em *emitter) adtLeanName(name string) (string, bool) {
	adt, ok := em.adts[name]
	if !ok || len(adt.TypeParams) != 0 {
		return "", false
	}
	if !em.usedTypes[name] {
		em.usedTypes[name] = true
	}
	return ident(name), true
}

// adtOfChecked names the ADT a checked type denotes, if it is one.
func (em *emitter) adtOfChecked(typ typechecker.Type) (string, bool) {
	switch t := typ.(type) {
	case *typechecker.ADTType:
		if _, known := em.adts[t.Name]; known {
			return t.Name, true
		}
	case *typechecker.GenericType:
		if len(t.TypeArgs) == 0 {
			if _, known := em.adts[t.Name]; known {
				return t.Name, true
			}
			return "", false
		}
		mangled, ok := atomOfType(t)
		if !ok {
			return "", false
		}
		if _, known := em.adts[mangled]; known {
			return mangled, true
		}
	case *typechecker.NarrowedADTVariantType:
		if len(t.TypeArgs) == 0 {
			if _, known := em.adts[t.ADTName]; known {
				return t.ADTName, true
			}
			return "", false
		}
		mangled, ok := atomOfType(&typechecker.GenericType{Name: t.ADTName, TypeArgs: t.TypeArgs})
		if !ok {
			return "", false
		}
		if _, known := em.adts[mangled]; known {
			return mangled, true
		}
	}
	return "", false
}

// typeReferences lists the ADT names a type expression mentions.
func (em *emitter) typeReferences(expr ast.Expression, out map[string]bool) {
	switch t := expr.(type) {
	case *ast.Identifier:
		if adt, ok := em.adts[t.Value]; ok && len(adt.TypeParams) == 0 {
			out[t.Value] = true
		}
	case *ast.IndexExpression:
		if t.Dot {
			return
		}
		if name, ok := em.applicationName(t); ok {
			out[name] = true
			_, args, _ := flattenApplication(t)
			for _, arg := range args {
				em.typeReferences(arg, out)
			}
			return
		}
		em.typeReferences(t.Left, out)
	}
}

// orderedTypes lists the ADTs to emit, dependencies first, otherwise in
// declaration order (instantiations after declarations, by mangled name).
func (em *emitter) orderedTypes(roots map[string]bool) []string {
	var ordered []string
	state := map[string]int{}
	var visit func(name string)
	visit = func(name string) {
		if state[name] != 0 {
			return
		}
		state[name] = 1
		adt := em.adts[name]
		refs := map[string]bool{}
		for _, variant := range adt.Variants {
			if variant.Payload != nil {
				em.typeReferences(variant.Payload, refs)
			}
			if record, ok := variant.Literal.(*ast.RecordLiteral); ok {
				for _, field := range record.FieldOrder {
					em.typeReferences(field.Value, refs)
				}
			}
		}
		names := make([]string, 0, len(refs))
		for ref := range refs {
			names = append(names, ref)
		}
		sort.Strings(names)
		for _, ref := range names {
			if ref != name {
				visit(ref)
			}
		}
		state[name] = 2
		ordered = append(ordered, name)
	}
	for _, name := range em.typeOrder {
		adt := em.adts[name]
		if len(adt.TypeParams) != 0 {
			continue
		}
		if em.usedTypes[name] || roots[name] {
			visit(name)
		}
	}
	return ordered
}

// emitSum renders a sum type as a Lean inductive.
func (em *emitter) emitSum(adt *ast.ADTType) (string, error) {
	var out strings.Builder
	fmt.Fprintf(&out, "inductive %s where\n", ident(adt.Name.Value))
	for _, variant := range adt.Variants {
		if variant.Payload == nil {
			fmt.Fprintf(&out, "  | %s\n", ident(variant.Name.Value))
			continue
		}
		typ, err := em.leanType(variant.Payload)
		if err != nil {
			return "", fmt.Errorf("lean: %s.%s: %w", adt.Name.Value, variant.Name.Value, err)
		}
		fmt.Fprintf(&out, "  | %s (payload : %s)\n", ident(variant.Name.Value), typ)
	}
	out.WriteString("  deriving Repr, Inhabited, BEq, DecidableEq\n")
	return out.String(), nil
}

// findVariant looks a variant up by name in an ADT declaration.
func findVariant(adt *ast.ADTType, name string) (*ast.ADTVariant, bool) {
	for _, variant := range adt.Variants {
		if variant.Name != nil && variant.Name.Value == name {
			return variant, true
		}
	}
	return nil, false
}

// variantTypeName names the concrete ADT a variant expression builds: the
// checked type when the checker recorded one, else the recorded resolution,
// else the type the context wants.
func (em *emitter) variantTypeName(expr *ast.VariantExpression, want string) (string, error) {
	if typ := em.env.CheckedExpressionType(expr); typ != nil {
		if name, ok := em.adtOfChecked(typ); ok {
			return name, nil
		}
	}
	if mangled, ok := em.tc.VariantResolution(expr); ok {
		if _, known := em.adts[mangled]; known {
			return mangled, nil
		}
	}
	if expr.TypeName != nil {
		if _, known := em.adts[expr.TypeName.Value]; known {
			return expr.TypeName.Value, nil
		}
	}
	if name, ok := em.leanNames[want]; ok {
		return name, nil
	}
	return "", fmt.Errorf("variant .%s has no concrete type in context", expr.Variant.Value)
}

// variant renders a variant construction.
func (em *emitter) variant(expr *ast.VariantExpression, want string) (string, error) {
	typeName, err := em.variantTypeName(expr, want)
	if err != nil {
		return "", err
	}
	adt := em.adts[typeName]
	variant, found := findVariant(adt, expr.Variant.Value)
	if !found {
		return "", fmt.Errorf("variant .%s is not declared by %s", expr.Variant.Value, typeName)
	}
	leanName, _ := em.adtLeanName(typeName)
	if expr.Payload == nil {
		if variant.Payload != nil {
			return "", fmt.Errorf("variant .%s of %s needs a payload", expr.Variant.Value, typeName)
		}
		return fmt.Sprintf("%s.%s", leanName, ident(variant.Name.Value)), nil
	}
	if variant.Payload == nil {
		return "", fmt.Errorf("variant .%s of %s takes no payload", expr.Variant.Value, typeName)
	}
	payloadType, err := em.leanType(variant.Payload)
	if err != nil {
		return "", err
	}
	term, err := em.expr(expr.Payload, payloadType)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("(%s.%s %s)", leanName, ident(variant.Name.Value), term), nil
}

// isVariantMatch recognizes a match over an ADT's variants: at least one
// variant pattern, the rest wildcards or a whole-value binding.
func isVariantMatch(match *ast.MatchExpression) bool {
	sawVariant := false
	for _, arm := range match.Arms {
		switch arm.Pattern.(type) {
		case *ast.VariantPattern:
			sawVariant = true
		case *ast.WildcardPattern, *ast.BindingPattern:
		default:
			return false
		}
	}
	return sawVariant
}

// scrutineeADT names the concrete ADT a variant match dispatches on.
func (em *emitter) scrutineeADT(match *ast.MatchExpression) (string, error) {
	if mangled, ok := em.tc.MatchResolution(match); ok {
		if _, known := em.adts[mangled]; known {
			return mangled, nil
		}
	}
	if typ := em.env.CheckedExpressionType(match.Scrutinee); typ != nil {
		if name, ok := em.adtOfChecked(typ); ok {
			return name, nil
		}
	}
	if id, ok := match.Scrutinee.(*ast.Identifier); ok {
		if leanType, known := em.scope.lookup(id.Value); known {
			if name, isADT := em.leanNames[leanType]; isADT {
				return name, nil
			}
		}
	}
	return "", fmt.Errorf("match over %s: scrutinee type is not an extracted ADT", match.Scrutinee.String())
}

// pattern renders a match pattern against an ADT, declaring its binders in
// the current scope.
func (em *emitter) pattern(p ast.Pattern, typeName string) (string, error) {
	adt := em.adts[typeName]
	switch pat := p.(type) {
	case *ast.WildcardPattern:
		return "_", nil
	case *ast.BindingPattern:
		if pat.Name == nil || pat.Name.Value == "_" {
			return "_", nil
		}
		leanName, _ := em.adtLeanName(typeName)
		em.scope.declare(pat.Name.Value, leanName)
		return ident(pat.Name.Value), nil
	case *ast.VariantPattern:
		variant, found := findVariant(adt, pat.Variant.Value)
		if !found {
			return "", fmt.Errorf("pattern .%s is not a variant of %s", pat.Variant.Value, typeName)
		}
		if pat.Payload == nil {
			if variant.Payload != nil {
				return "", fmt.Errorf("pattern .%s of %s omits its payload", pat.Variant.Value, typeName)
			}
			return "." + ident(variant.Name.Value), nil
		}
		if variant.Payload == nil {
			return "", fmt.Errorf("pattern .%s of %s takes no payload", pat.Variant.Value, typeName)
		}
		payloadType, err := em.leanType(variant.Payload)
		if err != nil {
			return "", err
		}
		switch inner := pat.Payload.(type) {
		case *ast.WildcardPattern:
			return fmt.Sprintf("(.%s _)", ident(variant.Name.Value)), nil
		case *ast.BindingPattern:
			if inner.Name == nil || inner.Name.Value == "_" {
				return fmt.Sprintf("(.%s _)", ident(variant.Name.Value)), nil
			}
			em.scope.declare(inner.Name.Value, payloadType)
			return fmt.Sprintf("(.%s %s)", ident(variant.Name.Value), ident(inner.Name.Value)), nil
		case *ast.VariantPattern:
			payloadADT, ok := em.leanNames[payloadType]
			if !ok {
				return "", fmt.Errorf("nested pattern %s: payload type %s is not an extracted ADT", inner.String(), payloadType)
			}
			nested, err := em.pattern(inner, payloadADT)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf("(.%s %s)", ident(variant.Name.Value), nested), nil
		case *ast.LiteralPattern:
			literal, err := em.expr(inner.Value, payloadType)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf("(.%s %s)", ident(variant.Name.Value), literal), nil
		}
		return "", fmt.Errorf("pattern %s is outside the extracted subset", pat.String())
	}
	return "", fmt.Errorf("pattern %s is outside the extracted subset", p.String())
}

// needsDo reports whether a conditional arm must be emitted as a do-block:
// it carries statements, or a call whose binding must not escape the arm.
func (em *emitter) needsDo(body ast.Expression) bool {
	needs := false
	walkExpressions(body, func(e ast.Expression) {
		switch x := e.(type) {
		case *ast.BlockExpression:
			if x.Block == nil {
				return
			}
			if len(x.Block.Statements) != 1 {
				needs = true
				return
			}
			if _, isExpr := x.Block.Statements[0].(*ast.ExpressionStatement); !isExpr {
				needs = true
			}
		case *ast.InvocationExpression:
			if callee, ok := x.Function.(*ast.Identifier); ok {
				if _, user := em.functions[callee.Value]; user {
					needs = true
				}
			}
		}
	})
	return needs
}

// matchArms renders the guarded arms of a variant match: each pattern with
// the scope its binders live in, ready for a value or a do-body.
type variantArm struct {
	pattern string
	scope   *scope
	body    ast.Expression
}

func (em *emitter) variantArms(match *ast.MatchExpression) (string, []variantArm, error) {
	typeName, err := em.scrutineeADT(match)
	if err != nil {
		return "", nil, err
	}
	leanName, _ := em.adtLeanName(typeName)
	scrutinee, err := em.expr(match.Scrutinee, leanName)
	if err != nil {
		return "", nil, err
	}
	var arms []variantArm
	for _, arm := range match.Arms {
		armScope := newScope(em.scope)
		saved := em.scope
		em.scope = armScope
		text, err := em.pattern(arm.Pattern, typeName)
		em.scope = saved
		if err != nil {
			return "", nil, err
		}
		arms = append(arms, variantArm{pattern: text, scope: armScope, body: arm.Body})
	}
	return scrutinee, arms, nil
}

// matchValue renders a variant match whose arms are plain values.
func (em *emitter) matchValue(match *ast.MatchExpression, want string) (string, error) {
	scrutinee, arms, err := em.variantArms(match)
	if err != nil {
		return "", err
	}
	var out strings.Builder
	fmt.Fprintf(&out, "(match %s with", scrutinee)
	for _, arm := range arms {
		saved := em.scope
		em.scope = arm.scope
		value, err := em.armValue(arm.body, want)
		em.scope = saved
		if err != nil {
			return "", err
		}
		fmt.Fprintf(&out, " | %s => %s", arm.pattern, value)
	}
	out.WriteString(")")
	return out.String(), nil
}

// matchStatement emits a variant match in statement position: the
// variables any arm assigns are rebound from the chosen arm.
func (em *emitter) matchStatement(match *ast.MatchExpression, lines *[]string, hoisted *[]string) error {
	scrutinee, arms, err := em.variantArms(match)
	if err != nil {
		return err
	}
	*lines = append(*lines, *hoisted...)
	*hoisted = nil
	var bodies []ast.Expression
	for _, arm := range arms {
		bodies = append(bodies, arm.body)
	}
	written := em.assignedOuter(bodies...)
	outs := tuple(identAll(written))
	if len(written) == 0 {
		outs = "()"
	}
	*lines = append(*lines, fmt.Sprintf("%slet %s ← (match %s with", em.indent, outs, scrutinee))
	for _, arm := range arms {
		*lines = append(*lines, fmt.Sprintf("%s  | %s => (do", em.indent, arm.pattern))
		saved, savedScope := em.indent, em.scope
		em.indent = saved + "    "
		em.scope = arm.scope
		var armLines []string
		err := em.branchBody(arm.body, &armLines)
		em.indent, em.scope = saved, savedScope
		if err != nil {
			return err
		}
		armLines = append(armLines, saved+"    pure "+outs+")")
		*lines = append(*lines, armLines...)
	}
	last := len(*lines) - 1
	(*lines)[last] += ")"
	return nil
}

// doValue renders a value-position conditional or variant match whose arms
// carry statements or calls: each arm is a do-block ending in its value,
// bound with the outer variables the arms assign, so nothing in an untaken
// arm is evaluated.
func (em *emitter) doValue(match *ast.MatchExpression, want string) (string, error) {
	if em.hoisted == nil {
		return "", fmt.Errorf("conditional %s in a position that cannot bind its result", match.String())
	}
	type doArm struct {
		head  string // "if c then" / "else if c then" / "else" / "| pattern =>"
		scope *scope
		body  ast.Expression
	}
	var arms []doArm
	var open string
	if isVariantMatch(match) {
		scrutinee, variantArms, err := em.variantArms(match)
		if err != nil {
			return "", err
		}
		open = fmt.Sprintf("(match %s with", scrutinee)
		for _, arm := range variantArms {
			arms = append(arms, doArm{head: "| " + arm.pattern + " =>", scope: arm.scope, body: arm.body})
		}
	} else {
		chain, err := em.branches(match)
		if err != nil {
			return "", err
		}
		open = "("
		for i, b := range chain {
			head := "else"
			switch {
			case i == 0:
				head = "if " + b.cond + " then"
			case b.cond != "":
				head = "else if " + b.cond + " then"
			}
			arms = append(arms, doArm{head: head, scope: newScope(em.scope), body: b.body})
		}
	}
	var bodies []ast.Expression
	for _, arm := range arms {
		bodies = append(bodies, arm.body)
	}
	written := em.assignedOuter(bodies...)
	em.temps++
	result := fmt.Sprintf("r%d", em.temps)
	outs := append([]string{result}, identAll(written)...)
	var lines []string
	lines = append(lines, fmt.Sprintf("%slet %s ← %s", em.indent, tuple(outs), open))
	for _, arm := range arms {
		lines = append(lines, fmt.Sprintf("%s  %s (do", em.indent, arm.head))
		saved, savedScope, savedHoisted := em.indent, em.scope, em.hoisted
		em.indent = saved + "    "
		em.scope = arm.scope
		var armLines []string
		em.hoisted = &armLines
		term, err := em.armResult(arm.body, want, &armLines)
		em.indent, em.scope, em.hoisted = saved, savedScope, savedHoisted
		if err != nil {
			return "", err
		}
		armLines = append(armLines, saved+"    pure "+tuple(append([]string{term}, identAll(written)...))+")")
		lines = append(lines, armLines...)
	}
	last := len(lines) - 1
	lines[last] += ")"
	*em.hoisted = append(*em.hoisted, lines...)
	return result, nil
}

// armResult emits an arm's statements into lines and returns its value
// term; a block's last statement is its value.
func (em *emitter) armResult(body ast.Expression, want string, lines *[]string) (string, error) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock {
		return em.expr(body, want)
	}
	if block.Block == nil || len(block.Block.Statements) == 0 {
		return "", fmt.Errorf("value-position block without a result")
	}
	statements := block.Block.Statements
	last, isExpr := statements[len(statements)-1].(*ast.ExpressionStatement)
	if !isExpr {
		return "", fmt.Errorf("value-position block does not end in its result expression")
	}
	if err := em.block(statements[:len(statements)-1], lines); err != nil {
		return "", err
	}
	// The result's own hoisted calls belong inside the arm.
	em.hoisted = lines
	return em.expr(last.Expression, want)
}
