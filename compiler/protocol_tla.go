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
	return &tlaEnv{payload: payload, initial: initial, lengths: env.lengths, records: env.records, root: root}
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
	seen := map[string]bool{}
	for _, step := range m.steps {
		if step.payload != nil {
			domain := domainName(step.payload.Name.Value)
			if !seen[domain] {
				seen[domain] = true
				constants = append(constants, domain)
			}
		}
	}
	if len(constants) > 0 {
		fmt.Fprintf(&b, "CONSTANTS %s\n\n", strings.Join(constants, ", "))
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
					if field, ok := dataField(store.Target); ok {
						if assigned[field] {
							return "", fmt.Errorf("protocol %s: %s from %s: effects assign %s twice", m.name, step.name, line.From.Value, field)
						}
						terms = append(terms, fmt.Sprintf("%s' = %s", field, value))
						assigned[field] = true
						continue
					}
					if field, indexExpr, ok := dataElement(store.Target); ok {
						index, err := tlaExpr(indexExpr, env.with(payload, false))
						if err != nil {
							return "", fmt.Errorf("protocol %s: %s from %s: effect index: %v", m.name, step.name, line.From.Value, err)
						}
						if _, seen := excepts[field]; !seen {
							fieldOrder = append(fieldOrder, field)
						}
						excepts[field] = append(excepts[field], fmt.Sprintf("![%s] = %s", index, value))
						continue
					}
					if field, indexExpr, sub, ok := dataElementField(store.Target); ok {
						// data.peers[i].acked = v folds into the element's record.
						index, err := tlaExpr(indexExpr, env.with(payload, false))
						if err != nil {
							return "", fmt.Errorf("protocol %s: %s from %s: effect index: %v", m.name, step.name, line.From.Value, err)
						}
						if _, seen := excepts[field]; !seen {
							fieldOrder = append(fieldOrder, field)
						}
						excepts[field] = append(excepts[field], fmt.Sprintf("![%s].%s = %s", index, sub, value))
						continue
					}
					return "", fmt.Errorf("protocol %s: %s from %s: effects: only `data.field = expr` and `data.field[i] = expr` translate", m.name, step.name, line.From.Value)
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
	b.WriteString("Spec == Init /\\ [][Next]_vars\n")
	b.WriteString(strings.Repeat("=", 77) + "\n")
	var head strings.Builder
	title := fmt.Sprintf(" MODULE %s ", m.name)
	pad := (77 - len(title)) / 2
	head.WriteString(strings.Repeat("-", pad) + title + strings.Repeat("-", 77-pad-len(title)) + "\n")
	fmt.Fprintf(&head, "\\* Generated by `oak protocol -tla %s` from %s. Do not edit: extend\n", m.name, origin)
	head.WriteString("\\* this module for liveness and environment assumptions, and regenerate.\n")
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

// dataElement recognizes `data.field[index]`.
func dataElement(target *ast.IndexExpression) (string, ast.Expression, bool) {
	if target == nil || target.Dot {
		return "", nil, false
	}
	inner, ok := target.Left.(*ast.IndexExpression)
	if !ok {
		return "", nil, false
	}
	field, isField := dataField(inner)
	if !isField {
		return "", nil, false
	}
	return field, target.Index, true
}

// dataElementField recognizes `data.field[index].sub`.
func dataElementField(target *ast.IndexExpression) (string, ast.Expression, string, bool) {
	if target == nil || !target.Dot {
		return "", nil, "", false
	}
	inner, ok := target.Left.(*ast.IndexExpression)
	sub, isSub := target.Index.(*ast.Identifier)
	if !ok || !isSub || sub == nil {
		return "", nil, "", false
	}
	field, indexExpr, isElement := dataElement(inner)
	if !isElement {
		return "", nil, "", false
	}
	return field, indexExpr, sub.Value, true
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
		for _, e := range lit.Elements {
			v, err := tlaExpr(e, env.with("", true))
			if err != nil {
				return "", err
			}
			rendered = append(rendered, v)
			if v != rendered[0] {
				same = false
			}
		}
		if same {
			return fmt.Sprintf("[k \\in 0..%d |-> %s]", length-1, rendered[0]), nil
		}
		var cases []string
		for i, v := range rendered {
			cases = append(cases, fmt.Sprintf("k = %d -> %s", i, v))
		}
		return fmt.Sprintf("[k \\in 0..%d |-> CASE %s]", length-1, strings.Join(cases, " [] ")), nil
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
		// A record element value (init of an array of records).
		var fields []string
		for _, f := range n.FieldOrder {
			v, err := tlaExpr(f.Value, env)
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
		if field, ok := dataField(n); ok {
			return field, nil
		}
		if field, indexExpr, ok := dataElement(n); ok {
			index, err := tlaExpr(indexExpr, env)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf("%s[%s]", field, index), nil
		}
		if field, indexExpr, sub, ok := dataElementField(n); ok {
			index, err := tlaExpr(indexExpr, env)
			if err != nil {
				return "", err
			}
			return fmt.Sprintf("%s[%s].%s", field, index, sub), nil
		}
		return "", fmt.Errorf("only data.field, data.field[i] and data.field[i].sub reads translate")
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
