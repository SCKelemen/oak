package compiler

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// Conformance of a hand-written TLA+ module against a protocol projection
// (docs/spec/112-protocols.md section 4a). Both texts are read into the
// projection's normal form — one action per step, one disjunct per line,
// each a conjunction of `state = "From"`, guard terms, `state' = "To"`,
// primed assignments, and UNCHANGED — and compared action by action. The
// verdict is the checker's: every difference is named with the action, the
// line, and both sides; a module using a form outside the normal form is
// reported as unsupported, never as conforming or as differing. TLC
// refinement remains the fallback for such modules.

// TLADifference is one place the two modules disagree.
type TLADifference struct {
	Kind   string `json:"kind"` // missing-action, extra-action, missing-line, extra-line, init, typeok, next, constants, variables
	Action string `json:"action,omitempty"`
	Line   int    `json:"line,omitempty"`  // 1-based disjunct index on the side that has it
	Left   string `json:"left,omitempty"`  // the projection's spelling
	Right  string `json:"right,omitempty"` // the hand-written module's spelling
}

// TLAConformance is the checker's report.
type TLAConformance struct {
	Protocol    string          `json:"protocol"`
	Conforms    bool            `json:"conforms"`
	Differences []TLADifference `json:"differences,omitempty"`
	Unsupported []string        `json:"unsupported,omitempty"`
}

// tlaLine is one disjunct of an action in normal form.
type tlaLine struct {
	From      string
	To        string
	Guards    []string // canonical, sorted
	Effects   []string // canonical `field' = expr`, sorted
	Unchanged []string // sorted
}

func (l tlaLine) key() string {
	return fmt.Sprintf("%s -> %s | %s | %s | %s", l.From, l.To, strings.Join(l.Guards, " /\\ "), strings.Join(l.Effects, " /\\ "), strings.Join(l.Unchanged, ","))
}

type tlaAction struct {
	Params []string
	Lines  []tlaLine
}

// tlaNormalForm is what both modules reduce to.
type tlaNormalForm struct {
	Constants []string
	Variables []string
	States    []string
	Init      []string // canonical terms, sorted
	Actions   map[string]*tlaAction
	Next      []string // canonical disjuncts, sorted
	TypeOK    []string // canonical terms, sorted
}

// ProtocolConformance renders the projection of decl and compares it with
// the hand-written module text.
func ProtocolConformance(decl *ast.ProtocolDeclaration, moduleText string, records map[string]*ast.RecordLiteral) (TLAConformance, error) {
	projected, err := ProtocolTLAWithRecords(decl, "projection", records)
	if err != nil {
		return TLAConformance{}, err
	}
	left, unsupportedLeft := parseTLAModule(projected)
	right, unsupportedRight := parseTLAModule(moduleText)
	report := TLAConformance{Protocol: decl.Name.Value}
	for _, u := range unsupportedLeft {
		report.Unsupported = append(report.Unsupported, "projection: "+u)
	}
	report.Unsupported = append(report.Unsupported, unsupportedRight...)
	report.Differences = compareTLA(left, right)
	report.Conforms = len(report.Differences) == 0 && len(report.Unsupported) == 0
	return report, nil
}

// parseTLAModule reads a module in the projection's normal form. Lines
// outside it are collected as unsupported with their line numbers.
func parseTLAModule(text string) (*tlaNormalForm, []string) {
	form := &tlaNormalForm{Actions: map[string]*tlaAction{}}
	var unsupported []string
	type definition struct {
		name   string
		params []string
		body   []string
		line   int
	}
	var definitions []*definition
	var current *definition
	for number, raw := range strings.Split(text, "\n") {
		line := strings.TrimRight(raw, " \t")
		trimmed := strings.TrimSpace(line)
		switch {
		case trimmed == "", strings.HasPrefix(trimmed, "\\*"), strings.HasPrefix(trimmed, "----"), strings.HasPrefix(trimmed, "===="):
			continue
		case strings.HasPrefix(trimmed, "EXTENDS "):
			continue
		case strings.HasPrefix(trimmed, "CONSTANTS ") || strings.HasPrefix(trimmed, "CONSTANT "):
			form.Constants = splitCommaList(strings.TrimSpace(trimmed[strings.Index(trimmed, " "):]))
			sort.Strings(form.Constants)
			continue
		case strings.HasPrefix(trimmed, "VARIABLES ") || strings.HasPrefix(trimmed, "VARIABLE "):
			form.Variables = splitCommaList(strings.TrimSpace(trimmed[strings.Index(trimmed, " "):]))
			continue
		}
		if !strings.HasPrefix(line, " ") && strings.Contains(trimmed, "==") {
			head := strings.TrimSpace(trimmed[:strings.Index(trimmed, "==")])
			rest := strings.TrimSpace(trimmed[strings.Index(trimmed, "==")+2:])
			name, params := head, []string(nil)
			if open := strings.Index(head, "("); open >= 0 && strings.HasSuffix(head, ")") {
				name = strings.TrimSpace(head[:open])
				params = splitCommaList(head[open+1 : len(head)-1])
			}
			current = &definition{name: name, params: params, line: number + 1}
			if rest != "" {
				current.body = append(current.body, rest)
			}
			definitions = append(definitions, current)
			continue
		}
		if current == nil {
			unsupported = append(unsupported, fmt.Sprintf("line %d: %q is outside any definition", number+1, trimmed))
			continue
		}
		current.body = append(current.body, trimmed)
	}
	for _, d := range definitions {
		body := strings.Join(d.body, " ")
		switch d.name {
		case "vars", "Spec":
			continue
		case "States":
			form.States = splitCommaList(strings.Trim(strings.TrimSpace(body), "{}"))
			sort.Strings(form.States)
		case "Init":
			form.Init = canonicalTerms(splitTopLevel(body, "/\\"))
		case "TypeOK":
			form.TypeOK = canonicalTerms(splitTopLevel(body, "/\\"))
		case "Next":
			form.Next = canonicalTerms(splitTopLevel(body, "\\/"))
		default:
			action := &tlaAction{Params: d.params}
			for _, disjunct := range splitTopLevel(body, "\\/") {
				line, problem := parseTLALine(disjunct)
				if problem != "" {
					unsupported = append(unsupported, fmt.Sprintf("line %d: action %s: %s", d.line, d.name, problem))
					continue
				}
				action.Lines = append(action.Lines, line)
			}
			form.Actions[d.name] = action
		}
	}
	return form, unsupported
}

// parseTLALine classifies one disjunct's conjuncts.
func parseTLALine(disjunct string) (tlaLine, string) {
	var line tlaLine
	for _, term := range splitTopLevel(disjunct, "/\\") {
		term = canonical(term)
		if term == "" {
			continue
		}
		switch {
		case strings.HasPrefix(term, "state=\""):
			line.From = strings.Trim(strings.TrimPrefix(term, "state="), "\"")
		case strings.HasPrefix(term, "state'=\""):
			line.To = strings.Trim(strings.TrimPrefix(term, "state'="), "\"")
		case strings.HasPrefix(term, "UNCHANGED<<") && strings.HasSuffix(term, ">>"):
			line.Unchanged = splitCommaList(strings.TrimSuffix(strings.TrimPrefix(term, "UNCHANGED<<"), ">>"))
			sort.Strings(line.Unchanged)
		case strings.HasPrefix(term, "UNCHANGED"):
			line.Unchanged = []string{strings.TrimPrefix(term, "UNCHANGED")}
		case strings.Contains(term, "'="):
			line.Effects = append(line.Effects, term)
		default:
			// A guard; a parenthesized conjunction is several guards.
			line.Guards = append(line.Guards, flattenConjunction(term)...)
		}
	}
	if line.From == "" || line.To == "" {
		return line, fmt.Sprintf("disjunct has no `state = \"From\"` and `state' = \"To\"`: %s", canonical(disjunct))
	}
	sort.Strings(line.Guards)
	sort.Strings(line.Effects)
	return line, ""
}

// splitTopLevel splits on an operator outside parentheses, braces,
// brackets, angle brackets and string literals.
func splitTopLevel(text, operator string) []string {
	var parts []string
	depth := 0
	inString := false
	start := 0
	for i := 0; i < len(text); i++ {
		c := text[i]
		if inString {
			if c == '"' {
				inString = false
			}
			continue
		}
		switch c {
		case '"':
			inString = true
		case '(', '{', '[':
			depth++
		case ')', '}', ']':
			depth--
		case '<':
			if i+1 < len(text) && text[i+1] == '<' {
				depth++
				i++
			}
		case '>':
			if i+1 < len(text) && text[i+1] == '>' {
				depth--
				i++
			}
		}
		if depth == 0 && strings.HasPrefix(text[i:], operator) {
			parts = append(parts, text[start:i])
			i += len(operator) - 1
			start = i + 1
		}
	}
	parts = append(parts, text[start:])
	var out []string
	for _, p := range parts {
		if strings.TrimSpace(p) != "" {
			out = append(out, p)
		}
	}
	return out
}

func splitCommaList(text string) []string {
	var out []string
	for _, part := range splitTopLevel(text, ",") {
		if p := strings.TrimSpace(part); p != "" {
			out = append(out, p)
		}
	}
	return out
}

// canonical removes whitespace and redundant parentheses so two spellings
// of one expression compare equal: outer parentheses, doubled parentheses,
// and parentheses around an operator-free operand (`~(parked[who])` is
// `~parked[who]`) are dropped; parentheses that group an operator
// expression inside a larger one stay.
func canonical(text string) string {
	compact := strings.Join(strings.Fields(text), "")
	compact = normalizeParens(compact)
	for strings.HasPrefix(compact, "(") && strings.HasSuffix(compact, ")") && balancedOuter(compact) {
		compact = normalizeParens(compact[1 : len(compact)-1])
	}
	return compact
}

// normalizeParens rewrites every top-level parenthesized group: the group's
// content is normalized recursively, an operator-free content loses its
// parentheses, a still-parenthesized content loses one layer.
func normalizeParens(text string) string {
	var b strings.Builder
	inString := false
	for i := 0; i < len(text); i++ {
		c := text[i]
		if inString {
			b.WriteByte(c)
			if c == '"' {
				inString = false
			}
			continue
		}
		if c == '"' {
			inString = true
			b.WriteByte(c)
			continue
		}
		if c != '(' {
			b.WriteByte(c)
			continue
		}
		end := matchingParen(text, i)
		if end < 0 {
			b.WriteString(text[i:])
			return b.String()
		}
		inner := normalizeParens(text[i+1 : end])
		for strings.HasPrefix(inner, "(") && strings.HasSuffix(inner, ")") && balancedOuter(inner) {
			inner = normalizeParens(inner[1 : len(inner)-1])
		}
		if operatorFree(inner) {
			b.WriteString(inner)
		} else {
			b.WriteString("(" + inner + ")")
		}
		i = end
	}
	return b.String()
}

func matchingParen(text string, open int) int {
	depth := 0
	inString := false
	for i := open; i < len(text); i++ {
		c := text[i]
		if inString {
			if c == '"' {
				inString = false
			}
			continue
		}
		switch c {
		case '"':
			inString = true
		case '(':
			depth++
		case ')':
			depth--
			if depth == 0 {
				return i
			}
		}
	}
	return -1
}

// operatorFree reports whether an expression has no top-level binary or
// prefix operator: an identifier, literal, string, or index/record access.
func operatorFree(text string) bool {
	depth := 0
	inString := false
	for i := 0; i < len(text); i++ {
		c := text[i]
		if inString {
			if c == '"' {
				inString = false
			}
			continue
		}
		switch c {
		case '"':
			inString = true
		case '(', '[', '{':
			depth++
		case ')', ']', '}':
			depth--
		case '<':
			if i+1 < len(text) && text[i+1] == '<' {
				depth++
				i++
				continue
			}
			if depth == 0 {
				return false
			}
		case '>':
			if i+1 < len(text) && text[i+1] == '>' {
				depth--
				i++
				continue
			}
			if depth == 0 {
				return false
			}
		case '/', '\\', '=', '#', '+', '-', '*', '%', '~', ':', '|':
			if depth == 0 {
				return false
			}
		}
	}
	return true
}

// flattenConjunction splits a canonical guard that is itself a conjunction
// into its conjuncts, so `((a) /\ b)` and `a /\ b` list the same guards.
func flattenConjunction(term string) []string {
	parts := splitTopLevel(term, "/\\")
	if len(parts) <= 1 {
		return []string{term}
	}
	var out []string
	for _, part := range parts {
		out = append(out, flattenConjunction(canonical(part))...)
	}
	return out
}

func balancedOuter(text string) bool {
	depth := 0
	for i := 0; i < len(text); i++ {
		switch text[i] {
		case '(':
			depth++
		case ')':
			depth--
			if depth == 0 && i != len(text)-1 {
				return false
			}
		}
	}
	return depth == 0
}

func canonicalTerms(terms []string) []string {
	out := make([]string, 0, len(terms))
	for _, term := range terms {
		if c := canonical(term); c != "" {
			out = append(out, c)
		}
	}
	sort.Strings(out)
	return out
}

func compareTLA(left, right *tlaNormalForm) []TLADifference {
	var diffs []TLADifference
	sortedNames := func(m map[string]*tlaAction) []string {
		names := make([]string, 0, len(m))
		for name := range m {
			names = append(names, name)
		}
		sort.Strings(names)
		return names
	}
	if strings.Join(left.Constants, ",") != strings.Join(right.Constants, ",") {
		diffs = append(diffs, TLADifference{Kind: "constants", Left: strings.Join(left.Constants, ", "), Right: strings.Join(right.Constants, ", ")})
	}
	if strings.Join(left.Variables, ",") != strings.Join(right.Variables, ",") {
		diffs = append(diffs, TLADifference{Kind: "variables", Left: strings.Join(left.Variables, ", "), Right: strings.Join(right.Variables, ", ")})
	}
	if strings.Join(left.States, ",") != strings.Join(right.States, ",") {
		diffs = append(diffs, TLADifference{Kind: "states", Left: strings.Join(left.States, ", "), Right: strings.Join(right.States, ", ")})
	}
	diffs = append(diffs, compareTermSets("init", left.Init, right.Init)...)
	diffs = append(diffs, compareTermSets("typeok", left.TypeOK, right.TypeOK)...)
	diffs = append(diffs, compareTermSets("next", left.Next, right.Next)...)
	for _, name := range sortedNames(left.Actions) {
		other, present := right.Actions[name]
		if !present {
			diffs = append(diffs, TLADifference{Kind: "missing-action", Action: name})
			continue
		}
		mine := left.Actions[name]
		if strings.Join(mine.Params, ",") != strings.Join(other.Params, ",") {
			diffs = append(diffs, TLADifference{Kind: "params", Action: name, Left: strings.Join(mine.Params, ", "), Right: strings.Join(other.Params, ", ")})
		}
		rightKeys := map[string]int{}
		for i, line := range other.Lines {
			rightKeys[line.key()] = i + 1
		}
		leftKeys := map[string]int{}
		for i, line := range mine.Lines {
			leftKeys[line.key()] = i + 1
			if _, has := rightKeys[line.key()]; !has {
				diffs = append(diffs, TLADifference{Kind: "missing-line", Action: name, Line: i + 1, Left: line.key(), Right: closestLine(line, other.Lines)})
			}
		}
		for i, line := range other.Lines {
			if _, has := leftKeys[line.key()]; !has {
				diffs = append(diffs, TLADifference{Kind: "extra-line", Action: name, Line: i + 1, Right: line.key(), Left: closestLine(line, mine.Lines)})
			}
		}
	}
	for _, name := range sortedNames(right.Actions) {
		if _, present := left.Actions[name]; !present {
			diffs = append(diffs, TLADifference{Kind: "extra-action", Action: name})
		}
	}
	return diffs
}

// closestLine names the line on the other side with the same from and to
// states, so a report shows what a changed guard or effect was changed from.
func closestLine(line tlaLine, candidates []tlaLine) string {
	for _, c := range candidates {
		if c.From == line.From && c.To == line.To {
			return c.key()
		}
	}
	return ""
}

func compareTermSets(kind string, left, right []string) []TLADifference {
	var diffs []TLADifference
	rightSet := map[string]bool{}
	for _, t := range right {
		rightSet[t] = true
	}
	leftSet := map[string]bool{}
	for _, t := range left {
		leftSet[t] = true
		if !rightSet[t] {
			diffs = append(diffs, TLADifference{Kind: kind, Left: t})
		}
	}
	for _, t := range right {
		if !leftSet[t] {
			diffs = append(diffs, TLADifference{Kind: kind, Right: t})
		}
	}
	return diffs
}

// FormatTLAConformance renders a report for the terminal.
func FormatTLAConformance(report TLAConformance) string {
	var b strings.Builder
	if report.Conforms {
		fmt.Fprintf(&b, "%s: the module agrees with the projection\n", report.Protocol)
		return b.String()
	}
	fmt.Fprintf(&b, "%s: the module does not agree with the projection\n", report.Protocol)
	for _, u := range report.Unsupported {
		fmt.Fprintf(&b, "  unsupported: %s\n", u)
	}
	for _, d := range report.Differences {
		where := d.Kind
		if d.Action != "" {
			where += " " + d.Action
			if d.Line > 0 {
				where += fmt.Sprintf(" line %d", d.Line)
			}
		}
		fmt.Fprintf(&b, "  %s\n", where)
		if d.Left != "" {
			fmt.Fprintf(&b, "    projection: %s\n", d.Left)
		}
		if d.Right != "" {
			fmt.Fprintf(&b, "    module:     %s\n", d.Right)
		}
	}
	return b.String()
}
