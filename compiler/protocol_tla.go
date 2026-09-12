package compiler

// TLA+ projection of a protocol declaration (docs/spec/112-protocols.md):
// one VARIABLE per data field plus the control state, one action per step
// name — the disjunction of its lines, each `state = From /\ guard /\ state'
// = To /\ effects /\ UNCHANGED rest` — Next with payloads quantified over
// declared constant domains, TypeOK, Init from the declared initial data,
// and Spec. Guards and effects translate from the Oak subset a protocol
// line may use (field reads, the payload, literals, conversions, arithmetic,
// comparisons, Boolean connectives, field assignment); anything else stops
// the export with a message naming the line. The module is complete for
// what the declaration says; a scenario extends it for liveness and
// environment assumptions, so regeneration never overwrites them.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// ProtocolTLA renders the TLA+ module of one declaration, or the shape
// diagnostics that stop it.
func ProtocolTLA(decl *ast.ProtocolDeclaration, origin string) (string, error) {
	return ProtocolTLAWithRecords(decl, origin, nil)
}

// tlaEnv carries what expression translation needs beyond the expression:
// the step's payload name, the lengths of array data fields (for
// quantifier bounds), the program's record declarations (for element
// records), and whether Cardinality was used (EXTENDS FiniteSets).
type tlaEnv struct {
	payload string
	initial bool
	// bound counts the enclosing function constructors of an init value,
	// so a nested array (a record's array field inside an array of
	// records) binds k, k1, k2 rather than shadowing k.
	bound   int
	lengths map[string]int64
	records map[string]*ast.RecordLiteral
	// finiteSets is shared by every derived env: set when Cardinality is
	// emitted anywhere in the module.
	finiteSets bool
	root       *tlaEnv
}

func (env *tlaEnv) with(payload string, initial bool) *tlaEnv {
	root := env.root
	if root == nil {
		root = env
	}
	return &tlaEnv{payload: payload, initial: initial, bound: env.bound, lengths: env.lengths, records: env.records, root: root}
}

// deeper is env inside one more function constructor.
func (env *tlaEnv) deeper() *tlaEnv {
	inner := env.with(env.payload, env.initial)
	inner.bound = env.bound + 1
	return inner
}

// boundVar names the bound variable at a nesting depth: k, k1, k2, ...
func boundVar(depth int) string {
	if depth == 0 {
		return "k"
	}
	return fmt.Sprintf("k%d", depth)
}

func (env *tlaEnv) useFiniteSets() {
	if env.root != nil {
		env.root.finiteSets = true
	}
	env.finiteSets = true
}

// ProtocolTLAWithRecords renders the module with the program's record
// declarations available for array-of-records data fields.
func ProtocolTLAWithRecords(decl *ast.ProtocolDeclaration, origin string, records map[string]*ast.RecordLiteral) (string, error) {
	var problems []string
	m, ok := analyzeProtocolWith(decl, records, func(code string, node ast.Node, format string, args ...interface{}) {
		problems = append(problems, fmt.Sprintf(format, args...))
	})
	if !ok {
		return "", fmt.Errorf("protocol %s: %s", decl.Name.Value, strings.Join(problems, "; "))
	}
	var fields []ast.RecordField
	if decl.Data != nil {
		fields = decl.Data.FieldOrder
	}
	signed := false
	for _, f := range fields {
		element := ""
		if id, isIdent := f.Value.(*ast.Identifier); isIdent {
			element = id.Value
		} else if _, e, ok := arrayShape(f.Value); ok {
			element = e
		}
		if strings.HasPrefix(element, "i") {
			signed = true
		}
	}
	env := &tlaEnv{lengths: map[string]int64{}, records: m.records}
	for _, f := range fields {
		if length, _, ok := arrayShape(f.Value); ok {
			env.lengths[f.Name] = length
		}
	}
	var b strings.Builder
	var constants []string
	var domains []string
	seen := map[string]bool{}
	for _, step := range m.steps {
		if step.payload != nil {
			domain := domainName(step.payload.Name.Value)
			if seen[domain] {
				continue
			}
			seen[domain] = true
			if fields, isRecord := payloadRecordFields(step.payload.Type, m.records); isRecord {
				// A record payload's domain is the record set of its
				// fields' domains, each a constant the configuration
				// assigns (TLC's configuration reads no record sets).
				var pairs []string
				for _, field := range fields {
					constants = append(constants, domain+fieldConstant(field.Name))
					pairs = append(pairs, fmt.Sprintf("%s: %s", field.Name, domain+fieldConstant(field.Name)))
				}
				domains = append(domains, fmt.Sprintf("%s == [%s]", domain, strings.Join(pairs, ", ")))
				continue
			}
			constants = append(constants, domain)
		}
	}
	if len(constants) > 0 {
		fmt.Fprintf(&b, "CONSTANTS %s\n\n", strings.Join(constants, ", "))
	}
	for _, domain := range domains {
		fmt.Fprintf(&b, "%s\n\n", domain)
	}
	vars := []string{"state"}
	for _, f := range fields {
		vars = append(vars, f.Name)
	}
	fmt.Fprintf(&b, "VARIABLES %s\n\n", strings.Join(vars, ", "))
	fmt.Fprintf(&b, "vars == <<%s>>\n\n", strings.Join(vars, ", "))
	quoted := make([]string, len(m.states))
	for i, st := range m.states {
		quoted[i] = fmt.Sprintf("%q", st)
	}
	fmt.Fprintf(&b, "States == {%s}\n\n", strings.Join(quoted, ", "))
	initTerms := []string{fmt.Sprintf("state = %q", m.initial)}
	if decl.Init != nil {
		for _, f := range fields {
			value, err := tlaInitValue(decl.Init.Fields[f.Name], f.Value, env)
			if err != nil {
				return "", fmt.Errorf("protocol %s: init %s: %v", m.name, f.Name, err)
			}
			initTerms = append(initTerms, fmt.Sprintf("%s = %s", f.Name, value))
		}
	}
	fmt.Fprintf(&b, "Init ==\n    %s\n\n", strings.Join(initTerms, "\n    /\\ "))
	var nextTerms []string
	for _, step := range m.steps {
		head := variantName(step.name)
		payload := ""
		if step.payload != nil {
			payload = step.payload.Name.Value
			head = fmt.Sprintf("%s(%s)", variantName(step.name), payload)
			nextTerms = append(nextTerms, fmt.Sprintf("(\\E %s \\in %s : %s)", payload, domainName(payload), head))
		} else {
			nextTerms = append(nextTerms, variantName(step.name))
		}
		fmt.Fprintf(&b, "%s ==\n", head)
		for i, line := range step.lines {
			terms := []string{fmt.Sprintf("state = %q", line.From.Value)}
			if line.Guard != nil {
				guard, err := tlaExpr(line.Guard, env.with(payload, false))
				if err != nil {
					return "", fmt.Errorf("protocol %s: %s from %s: guard: %v", m.name, step.name, line.From.Value, err)
				}
				terms = append(terms, guard)
			}
			terms = append(terms, fmt.Sprintf("state' = %q", line.To.Value))
			assigned := map[string]bool{}
			if line.Effects != nil {
				// Whole-field stores become `field' = value`; element stores
				// on one array field fold into one `[field EXCEPT ![i] = v, ...]`.
				var fieldOrder []string
				excepts := map[string][]string{}
				for _, stmt := range line.Effects.Statements {
					store, isStore := stmt.(*ast.IndexAssignmentStatement)
					if !isStore {
						return "", fmt.Errorf("protocol %s: %s from %s: effects: only `data.field = expr` and `data.field[i] = expr` translate", m.name, step.name, line.From.Value)
					}
					value, err := tlaExpr(store.Value, env.with(payload, false))
					if err != nil {
						return "", fmt.Errorf("protocol %s: %s from %s: effect: %v", m.name, step.name, line.From.Value, err)
					}
					field, selector, err := tlaDataPath(store.Target, env.with(payload, false))
					if err != nil {
						return "", fmt.Errorf("protocol %s: %s from %s: effects: %v", m.name, step.name, line.From.Value, err)
					}
					if selector == "" {
						if assigned[field] {
							return "", fmt.Errorf("protocol %s: %s from %s: effects assign %s twice", m.name, step.name, line.From.Value, field)
						}
						terms = append(terms, fmt.Sprintf("%s' = %s", field, value))
						assigned[field] = true
						continue
					}
					// A store below the field — data.f[i], data.f[i].sub,
					// data.f.sub[j], any depth — folds into one EXCEPT on
					// the field with the path as its selector.
					if _, seen := excepts[field]; !seen {
						fieldOrder = append(fieldOrder, field)
					}
					excepts[field] = append(excepts[field], fmt.Sprintf("!%s = %s", selector, value))
					continue
				}
				for _, field := range fieldOrder {
					if assigned[field] {
						return "", fmt.Errorf("protocol %s: %s from %s: effects assign %s whole and by element", m.name, step.name, line.From.Value, field)
					}
					terms = append(terms, fmt.Sprintf("%s' = [%s EXCEPT %s]", field, field, strings.Join(excepts[field], ", ")))
					assigned[field] = true
				}
			}
			var unchanged []string
			for _, f := range fields {
				if !assigned[f.Name] {
					unchanged = append(unchanged, f.Name)
				}
			}
			if len(unchanged) > 0 {
				terms = append(terms, fmt.Sprintf("UNCHANGED <<%s>>", strings.Join(unchanged, ", ")))
			}
			connector := "    "
			if len(step.lines) > 1 {
				connector = "    \\/ "
			}
			_ = i
			fmt.Fprintf(&b, "%s%s\n", connector, strings.Join(terms, " /\\ "))
		}
		b.WriteString("\n")
	}
	fmt.Fprintf(&b, "Next ==\n    %s\n\n", strings.Join(nextTerms, "\n    \\/ "))
	typeTerms := []string{"state \\in States"}
	for _, f := range fields {
		typeTerms = append(typeTerms, fmt.Sprintf("%s \\in %s", f.Name, tlaDomainWith(f.Value, env.records)))
	}
	fmt.Fprintf(&b, "TypeOK ==\n    %s\n\n", strings.Join(typeTerms, "\n    /\\ "))
	// Declared fairness joins the specification: weak or strong fairness
	// on each named step, its payload quantified; declared liveness is the
	// `Liveness` property, `<>` for a target alone and `~>` (leads to) for
	// a from -> target pair (docs/spec/112-protocols.md section 4).
	spec := []string{"Init", "[][Next]_vars"}
	for _, f := range decl.Fairness {
		action := variantName(f.Step.Value)
		for _, step := range m.steps {
			if step.name == f.Step.Value && step.payload != nil {
				payload := step.payload.Name.Value
				action = fmt.Sprintf("\\E %s \\in %s : %s(%s)", payload, domainName(payload), action, payload)
			}
		}
		form := "WF"
		if f.Strong {
			form = "SF"
		}
		spec = append(spec, fmt.Sprintf("%s_vars(%s)", form, action))
	}
	fmt.Fprintf(&b, "Spec == %s\n", strings.Join(spec, " /\\ "))
	if len(decl.Liveness) > 0 {
		term := func(side ast.Expression) (string, error) {
			if state, isState := livenessState(side); isState {
				return fmt.Sprintf("state = %q", state), nil
			}
			return tlaExpr(side, env.with("", false))
		}
		var terms []string
		for _, l := range decl.Liveness {
			target, err := term(l.Target)
			if err != nil {
				return "", fmt.Errorf("protocol %s: eventually: %v", m.name, err)
			}
			if l.From == nil {
				terms = append(terms, fmt.Sprintf("<>(%s)", target))
				continue
			}
			from, err := term(l.From)
			if err != nil {
				return "", fmt.Errorf("protocol %s: eventually: %v", m.name, err)
			}
			terms = append(terms, fmt.Sprintf("((%s) ~> (%s))", from, target))
		}
		fmt.Fprintf(&b, "\nLiveness ==\n    %s\n", strings.Join(terms, "\n    /\\ "))
	}
	b.WriteString(strings.Repeat("=", 77) + "\n")
	var head strings.Builder
	title := fmt.Sprintf(" MODULE %s ", m.name)
	pad := (77 - len(title)) / 2
	head.WriteString(strings.Repeat("-", pad) + title + strings.Repeat("-", 77-pad-len(title)) + "\n")
	fmt.Fprintf(&head, "\\* Generated by `oak protocol -tla %s` from %s. Do not edit: extend\n", m.name, origin)
	head.WriteString("\\* this module for environment assumptions beyond the declared fairness,\n\\* and regenerate.\n")
	extends := "Naturals"
	if signed {
		extends = "Integers"
	}
	if env.finiteSets {
		extends += ", FiniteSets"
	}
	fmt.Fprintf(&head, "EXTENDS %s\n\n", extends)
	return head.String() + b.String(), nil
}

// ProtocolTLCConfig is the TLC configuration for the module ProtocolTLA
// renders: the specification, the type invariant, the declared liveness
// property when there is one, and a small domain for each payload constant
// (Bool's two values; four values for a scalar) that a model widens as it
// needs.
func ProtocolTLCConfig(decl *ast.ProtocolDeclaration) string {
	return ProtocolTLCConfigWith(decl, nil)
}

// payloadDomain is the small model domain of a scalar payload or field:
// four values for an integer, both Booleans.
func payloadDomain(typ ast.Expression) string {
	if typeName, isIdent := typ.(*ast.Identifier); isIdent && typeName.Value == "Bool" {
		return "{TRUE, FALSE}"
	}
	return "{0, 1, 2, 3}"
}

// payloadRecordFields is the field list of a record payload type.
func payloadRecordFields(typ ast.Expression, records map[string]*ast.RecordLiteral) ([]ast.RecordField, bool) {
	typeName, isIdent := typ.(*ast.Identifier)
	if !isIdent {
		return nil, false
	}
	record, isRecord := records[typeName.Value]
	if !isRecord {
		return nil, false
	}
	return record.FieldOrder, true
}

// fieldConstant names a record payload field's domain constant: Cmd + Slot.
func fieldConstant(field string) string {
	if field == "" {
		return ""
	}
	return strings.ToUpper(field[:1]) + field[1:]
}

// ProtocolTLCConfigWith is ProtocolTLCConfig with the program's record
// declarations, so a record payload's domain is the record set of its
// fields' domains.
func ProtocolTLCConfigWith(decl *ast.ProtocolDeclaration, records map[string]*ast.RecordLiteral) string {
	var b strings.Builder
	b.WriteString("SPECIFICATION Spec\nINVARIANT TypeOK\n")
	if len(decl.Liveness) > 0 {
		b.WriteString("PROPERTY Liveness\n")
	}
	seen := map[string]bool{}
	var constants []string
	for _, t := range decl.Transitions {
		if t.Param == nil {
			continue
		}
		domain := domainName(t.Param.Name.Value)
		if seen[domain] {
			continue
		}
		seen[domain] = true
		if fields, isRecord := payloadRecordFields(t.Param.Type, records); isRecord {
			for _, field := range fields {
				constants = append(constants, fmt.Sprintf("    %s%s = %s", domain, fieldConstant(field.Name), payloadDomain(field.Value)))
			}
			continue
		}
		constants = append(constants, fmt.Sprintf("    %s = %s", domain, payloadDomain(t.Param.Type)))
	}
	if len(constants) > 0 {
		b.WriteString("CONSTANTS\n" + strings.Join(constants, "\n") + "\n")
	}
	return b.String()
}

// domainName is the constant naming a payload's domain: compare -> Compare.
func domainName(param string) string {
	if param == "" {
		return "Payload"
	}
	return strings.ToUpper(param[:1]) + param[1:]
}

// tlaDomain maps a field's Oak type to its TLA+ set; an `[N]T` field is a
// function from 0..N-1 into T's set.
func tlaDomain(typ ast.Expression) string {
	return tlaDomainWith(typ, nil)
}

// tlaDomainWith is tlaDomain with the program's record declarations: an
// element record R becomes the record set [f1: D1, f2: D2].
func tlaDomainWith(typ ast.Expression, records map[string]*ast.RecordLiteral) string {
	if length, element, ok := arrayShape(typ); ok {
		return fmt.Sprintf("[0..%d -> %s]", length-1, tlaDomainWith(&ast.Identifier{Value: element}, records))
	}
	id, ok := typ.(*ast.Identifier)
	if !ok {
		return "Nat"
	}
	if record, isRecord := records[id.Value]; isRecord {
		var fields []string
		for _, f := range record.FieldOrder {
			fields = append(fields, fmt.Sprintf("%s: %s", f.Name, tlaDomainWith(f.Value, records)))
		}
		return "[" + strings.Join(fields, ", ") + "]"
	}
	switch id.Value {
	case "Bool":
		return "BOOLEAN"
	case "i8", "i16", "i32", "i64":
		return "Int"
	default:
		return "Nat"
	}
}

// dataField recognizes `data.field`.
func dataField(target *ast.IndexExpression) (string, bool) {
	if target == nil || !target.Dot {
		return "", false
	}
	base, okBase := target.Left.(*ast.Identifier)
	field, okField := target.Index.(*ast.Identifier)
	if !okBase || !okField || base.Value != "data" {
		return "", false
	}
	return field.Value, true
}

// tlaDataPath reads a data path of any depth rooted at `data.field`: the
// field, and the TLA+ selector below it (`[i]`, `.sub`, `[i].log[j]`), as
// EXCEPT spells it and as a read spells it after the variable.
func tlaDataPath(target *ast.IndexExpression, env *tlaEnv) (field, selector string, err error) {
	if target == nil {
		return "", "", fmt.Errorf("only data.field paths translate")
	}
	if name, ok := dataField(target); ok {
		return name, "", nil
	}
	inner, ok := target.Left.(*ast.IndexExpression)
	if !ok {
		return "", "", fmt.Errorf("only data.field paths translate, not %s", target.String())
	}
	field, prefix, err := tlaDataPath(inner, env)
	if err != nil {
		return "", "", err
	}
	if target.Dot {
		sub, isIdent := target.Index.(*ast.Identifier)
		if !isIdent {
			return "", "", fmt.Errorf("a field selector names a field, not %s", target.Index.String())
		}
		return field, prefix + "." + sub.Value, nil
	}
	index, err := tlaExpr(target.Index, env)
	if err != nil {
		return "", "", err
	}
	return field, prefix + "[" + index + "]", nil
}

// payloadField recognizes `payload.field`, a read of a record payload.
func payloadField(target *ast.IndexExpression, payload string) (string, bool) {
	if target == nil || !target.Dot || payload == "" {
		return "", false
	}
	base, okBase := target.Left.(*ast.Identifier)
	field, okField := target.Index.(*ast.Identifier)
	if !okBase || !okField || base.Value != payload {
		return "", false
	}
	return field.Value, true
}

// arrayShape reads `[N]T` (an index expression over the element type).
func arrayShape(typ ast.Expression) (length int64, element string, ok bool) {
	idx, isIdx := typ.(*ast.IndexExpression)
	if !isIdx || idx.Dot {
		return 0, "", false
	}
	n, isLen := idx.Index.(*ast.IntegerLiteral)
	elem, isElem := idx.Left.(*ast.Identifier)
	if !isLen || !isElem {
		return 0, "", false
	}
	return n.Value, elem.Value, true
}

// tlaInitValue renders an init value: a scalar, or an array literal as a
// function over 0..N-1 (one arrow when every element is the same).
func tlaInitValue(value ast.Expression, typ ast.Expression, env *tlaEnv) (string, error) {
	if lit, isArray := value.(*ast.ArrayLiteral); isArray {
		length, _, ok := arrayShape(typ)
		if !ok {
			return "", fmt.Errorf("array init for a non-array field")
		}
		if int64(len(lit.Elements)) != length {
			return "", fmt.Errorf("array init has %d elements, the field %d", len(lit.Elements), length)
		}
		var rendered []string
		same := true
		inner := env.with("", true).deeper()
		for _, e := range lit.Elements {
			v, err := tlaExpr(e, inner)
			if err != nil {
				return "", err
			}
			rendered = append(rendered, v)
			if v != rendered[0] {
				same = false
			}
		}
		k := boundVar(env.bound)
		if same {
			return fmt.Sprintf("[%s \\in 0..%d |-> %s]", k, length-1, rendered[0]), nil
		}
		var cases []string
		for i, v := range rendered {
			cases = append(cases, fmt.Sprintf("%s = %d -> %s", k, i, v))
		}
		return fmt.Sprintf("[%s \\in 0..%d |-> CASE %s]", k, length-1, strings.Join(cases, " [] ")), nil
	}
	return tlaExpr(value, env.with("", true))
}

var tlaOperators = map[string]string{
	"&&": "/\\", "||": "\\/", "==": "=", "!=": "#", "<": "<", "<=": "<=", ">": ">", ">=": ">=",
	"+": "+", "-": "-", "*": "*", "/": "\\div", "%": "%",
}

var conversionNames = map[string]bool{"u8": true, "u16": true, "u32": true, "u64": true, "i8": true, "i16": true, "i32": true, "i64": true}

// tlaExpr translates the guard/effect expression subset. `payload` is the
// step's parameter name (or ""); `initial` marks init values, where only
// literals and conversions of literals are meaningful.
func tlaExpr(e ast.Expression, env *tlaEnv) (string, error) {
	payload := env.payload
	switch n := e.(type) {
	case *ast.RecordLiteral:
		// A record element value (init of an array of records); an array
		// field of the record is a function, by the declared field type.
		var declared *ast.RecordLiteral
		if n.TypeName != nil && env.records != nil {
			declared = env.records[n.TypeName.Value]
		}
		var fields []string
		for _, f := range n.FieldOrder {
			var v string
			var err error
			if _, isArray := f.Value.(*ast.ArrayLiteral); isArray && declared != nil {
				v, err = tlaInitValue(f.Value, declared.Fields[f.Name], env)
			} else {
				v, err = tlaExpr(f.Value, env)
			}
			if err != nil {
				return "", err
			}
			fields = append(fields, fmt.Sprintf("%s |-> %s", f.Name, v))
		}
		return "[" + strings.Join(fields, ", ") + "]", nil
	case *ast.IntegerLiteral:
		return fmt.Sprintf("%d", n.Value), nil
	case *ast.Boolean:
		if n.Value {
			return "TRUE", nil
		}
		return "FALSE", nil
	case *ast.Identifier:
		if n.Value == payload && payload != "" {
			return n.Value, nil
		}
		return "", fmt.Errorf("identifier %s is not the payload or a data field", n.Value)
	case *ast.IndexExpression:
		if field, ok := payloadField(n, payload); ok {
			// A record payload's field reads as the TLA+ record field.
			return payload + "." + field, nil
		}
		// A data path of any depth — data.f, data.f[i], data.f[i].sub,
		// data.f.sub[j] — reads as the same path over the variable.
		field, selector, err := tlaDataPath(n, env)
		if err != nil {
			return "", err
		}
		return field + selector, nil
	case *ast.InvocationExpression:
		fn, ok := n.Function.(*ast.Identifier)
		if ok && conversionNames[fn.Value] && len(n.Arguments) == 1 {
			return tlaExpr(n.Arguments[0], env)
		}
		if form, field, sub, isQuantifier := quantifierCall(n); isQuantifier && field != "" {
			// count/all/any/none over an array field: Cardinality of the
			// true slots, or a bounded quantifier (112-protocols.md section 4).
			length, known := env.lengths[field]
			if !known {
				return "", fmt.Errorf("%s over data.%s, which is not an array field", form, field)
			}
			element := fmt.Sprintf("%s[k]", field)
			if sub != "" {
				element += "." + sub
			}
			bound := fmt.Sprintf("k \\in 0..%d", length-1)
			switch form {
			case "count":
				env.useFiniteSets()
				return fmt.Sprintf("Cardinality({%s : %s})", bound, element), nil
			case "all":
				return fmt.Sprintf("(\\A %s : %s)", bound, element), nil
			case "any":
				return fmt.Sprintf("(\\E %s : %s)", bound, element), nil
			case "none":
				return fmt.Sprintf("(\\A %s : ~%s)", bound, element), nil
			}
		}
		return "", fmt.Errorf("calls other than width conversions and count/all/any/none do not translate")
	case *ast.PrefixExpression:
		inner, err := tlaExpr(n.Right, env)
		if err != nil {
			return "", err
		}
		switch n.Operator {
		case "!":
			return "~(" + inner + ")", nil
		case "-":
			return "-(" + inner + ")", nil
		}
		return "", fmt.Errorf("prefix operator %s does not translate", n.Operator)
	case *ast.InfixExpression:
		op, ok := tlaOperators[n.Operator]
		if !ok {
			return "", fmt.Errorf("operator %s does not translate", n.Operator)
		}
		left, err := tlaExpr(n.Left, env)
		if err != nil {
			return "", err
		}
		right, err := tlaExpr(n.Right, env)
		if err != nil {
			return "", err
		}
		return "(" + left + " " + op + " " + right + ")", nil
	}
	return "", fmt.Errorf("expression %T does not translate", e)
}

// sortedFieldNames is a deterministic helper for diagnostics.
func sortedFieldNames(fields map[string]ast.Expression) []string {
	names := make([]string, 0, len(fields))
	for name := range fields {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}
