package repl

// Lean statements for a session's obligations (docs/spec/83-modules.md
// section 10, docs/spec/85-discipline.md). The compiler records what it
// could not discharge; this file states each record as a Lean theorem over
// the formal models in spec/lean so the programmer proves it there:
//
//   - OAK-D0103 (unbounded loop): the loop is translated into Oak.Loops —
//     guard, variable representations, and the body as one simultaneous
//     assignment obtained by symbolic execution — and its termination from
//     every start is the statement. Loops outside the translatable fragment
//     are reported, never approximated.
//   - OAK-D0102 (tail cycle): the cycle's call edges are stated over
//     Oak.Discipline.Ranked, and the compiler's own rank certificate
//     discharges them, so the theorem is emitted proved.
//   - OAK-B0110 (unsafe disjointness): the two writable regions are stated
//     over Oak.Regions.Disjoint; known regions decide (an admitted
//     assumption that is false fails to elaborate), symbolic ones become
//     variables.
//
// The REPL emits the file; Lean checks it. The compiler proves nothing here.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/borrowchecker"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/modules"
)

// LeanObligations renders every open obligation of the session as a Lean
// file importing the governing models. The result elaborates under the
// repository's `lake build`; theorems whose discharge needs a programmer's
// argument carry `sorry` with the discharge skeleton in a comment.
func (s *Session) LeanObligations() (string, error) {
	model, err := compiler.New().
		WithSessionSources(s.ModuleDir, map[string]string{"repl.oak": s.Source()}).
		WithPlatformSizes(s.IntSize, s.PtrSize).
		SemanticModel().Get()
	if err != nil {
		return "", err
	}
	var out strings.Builder
	out.WriteString("import Oak.Loops\nimport Oak.Discipline\nimport Oak.Regions\n\n")
	out.WriteString("/-! Obligations of an Oak REPL session, stated by `:lean`. Each theorem is one\nrecorded assumption the compiler could not discharge; proving it here discharges\nit. Generated — edit the proofs, regenerate the statements. -/\n\n")
	out.WriteString("namespace Oak.Session\n\n")
	count := 0

	// OAK-D0103: loops without a statically evident bound.
	for index, unbounded := range discipline.UnboundedLoops(model.Tree.Root) {
		count++
		name := fmt.Sprintf("loop_%s_%d", identifierPart(unbounded.Function), index+1)
		line := unbounded.Loop.Token.Line
		translation, reason := translateLoop(unbounded.Loop, unbounded.Function, model.Tree.Root)
		fmt.Fprintf(&out, "/-- OAK-D0103: the loop in `%s` at repl.oak:%d has no statically evident bound. -/\n", unbounded.Function, line)
		if translation == nil {
			fmt.Fprintf(&out, "-- Not translatable into Oak.Loops: %s.\n-- State the loop's termination by hand over Oak.Loops or Oak.BoundedLoop.\n\n", reason)
			continue
		}
		fmt.Fprintf(&out, "-- variables: %s\n", translation.variableLegend())
		fmt.Fprintf(&out, "def %s : Oak.Loops.Loop :=\n  { guard := %s,\n    body := [%s] }\n\n", name, translation.guard, strings.Join(translation.assigns, ",\n            "))
		fmt.Fprintf(&out, "theorem %s_terminates : ∀ env, Oak.Loops.Terminates %s env := by\n", name, name)
		fmt.Fprintf(&out, "  -- Discharge: exact Oak.Loops.ranking_terminates %s (fun env => <rank>) (by intro env h; <decrease>)\n", name)
		out.WriteString("  sorry\n\n")
	}

	// OAK-D0102: tail-only cycles, discharged by the recorded certificate.
	analysis := discipline.AnalyzeProgram(model.Tree.Root)
	for index, cycle := range analysis.TailCycles {
		count++
		members := map[string]int{}
		for i, member := range cycle.Members {
			members[member] = i
		}
		edges := make([]string, 0, len(cycle.Edges))
		for _, edge := range cycle.Edges {
			edges = append(edges, fmt.Sprintf("(%d, %d)", members[edge.Caller], members[edge.Callee]))
		}
		sort.Strings(edges)
		name := fmt.Sprintf("cycle_%d", index+1)
		legend := make([]string, 0, len(cycle.Members))
		for i, member := range cycle.Members {
			legend = append(legend, fmt.Sprintf("%d ↦ `%s`", i, modules.DemangleText(member)))
		}
		fmt.Fprintf(&out, "/-- OAK-D0102: tail recursion through %s relies on tail-call elimination.\nFunctions: %s. Every internal call is a tail call, so the constant rank\ncertificate the compiler computed satisfies Oak.Discipline.Ranked. -/\n", strings.Join(demangleAll(cycle.Members), ", "), strings.Join(legend, ", "))
		fmt.Fprintf(&out, "theorem %s_ranked : ∃ rank : Nat → Nat, Oak.Discipline.Ranked [] [%s] rank :=\n  ⟨fun _ => 0, by simp [Oak.Discipline.Ranked]⟩\n\n", name, strings.Join(edges, ", "))
	}

	// OAK-B0110: admitted writable-disjointness assumptions.
	index := 0
	for _, d := range model.Diagnostics {
		if d == nil || d.Code != string(borrowchecker.CodeUnsafeAssumption) {
			continue
		}
		data, ok := d.Data.(borrowchecker.UnsafeAssumptionData)
		if !ok {
			continue
		}
		index++
		count++
		name := fmt.Sprintf("unsafe_%d", index)
		fmt.Fprintf(&out, "/-- OAK-B0110 at repl.oak:%d: %s -/\n", d.Range.Start.Line+1, strings.ReplaceAll(d.Title, "-/", "- /"))
		switch {
		case data.Requested.Known && data.Existing.Known:
			requested := fmt.Sprintf("⟨%d, %d⟩", data.Requested.Lo, data.Requested.Hi)
			existing := fmt.Sprintf("⟨%d, %d⟩", data.Existing.Lo, data.Existing.Hi)
			if regionsDisjoint(data.Requested, data.Existing) {
				fmt.Fprintf(&out, "theorem %s_disjoint : Oak.Regions.Disjoint %s %s := by decide\n\n", name, requested, existing)
			} else {
				fmt.Fprintf(&out, "-- The regions overlap: the admitted assumption is false.\ntheorem %s_overlaps : ¬ Oak.Regions.Disjoint %s %s := by decide\n\n", name, requested, existing)
			}
		default:
			fmt.Fprintf(&out, "-- `%s` is %s, `%s` is %s; constrain the symbolic region(s) and prove.\n", data.RequestedName, describeFact(data.Requested), data.ExistingName, describeFact(data.Existing))
			fmt.Fprintf(&out, "theorem %s_disjoint (requested existing : Oak.Regions.Region)%s :\n    Oak.Regions.Disjoint requested existing := by\n  sorry\n\n", name, factHypotheses(data))
		}
	}

	if count == 0 {
		out.WriteString("-- No recorded assumptions: every check in the session is discharged statically or trapped at runtime.\n\n")
	}
	out.WriteString("end Oak.Session\n")
	return out.String(), nil
}

func regionsDisjoint(a, b borrowchecker.RegionFact) bool {
	return a.Hi <= b.Lo || b.Hi <= a.Lo || a.Hi <= a.Lo || b.Hi <= b.Lo
}

func describeFact(fact borrowchecker.RegionFact) string {
	if fact.Known {
		return fmt.Sprintf("[%d, %d)", fact.Lo, fact.Hi)
	}
	return "a symbolic region"
}

func factHypotheses(data borrowchecker.UnsafeAssumptionData) string {
	var parts []string
	if data.Requested.Known {
		parts = append(parts, fmt.Sprintf(" (hr : requested = ⟨%d, %d⟩)", data.Requested.Lo, data.Requested.Hi))
	}
	if data.Existing.Known {
		parts = append(parts, fmt.Sprintf(" (he : existing = ⟨%d, %d⟩)", data.Existing.Lo, data.Existing.Hi))
	}
	return strings.Join(parts, "")
}

func demangleAll(names []string) []string {
	out := make([]string, 0, len(names))
	for _, name := range names {
		out = append(out, "`"+modules.DemangleText(name)+"`")
	}
	return out
}

func identifierPart(name string) string {
	if name == "" {
		return "toplevel"
	}
	var b strings.Builder
	for _, r := range modules.DemangleText(name) {
		switch {
		case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z', r >= '0' && r <= '9':
			b.WriteRune(r)
		default:
			b.WriteByte('_')
		}
	}
	return b.String()
}

// loopTranslation is a loop rendered in Oak.Loops terms.
type loopTranslation struct {
	guard     string
	assigns   []string
	variables []string // index -> source name
}

func (t *loopTranslation) variableLegend() string {
	parts := make([]string, 0, len(t.variables))
	for i, name := range t.variables {
		parts = append(parts, fmt.Sprintf("%d ↦ `%s`", i, name))
	}
	return strings.Join(parts, ", ")
}

// translator symbolically executes a loop body over the fragment Oak.Loops
// models. Every variable is an index; state maps each assigned index to
// the Lean expression of its value in terms of pre-iteration values.
type translator struct {
	program   *ast.Program
	function  string
	names     map[string]int
	variables []string
	types     map[string]string // Lean Ty per variable, "" unknown
	err       string
}

// translateLoop returns the translation or the reason none exists.
func translateLoop(loop *ast.WhileStatement, function string, program *ast.Program) (*loopTranslation, string) {
	t := &translator{program: program, function: function, names: map[string]int{}, types: map[string]string{}}
	guard := t.expr(loop.Condition, nil)
	if t.err != "" {
		return nil, t.err
	}
	state, assigned := map[string]string{}, map[string]string{}
	var order []string
	t.block(loop.Body, state, &order, assigned)
	if t.err != "" {
		return nil, t.err
	}
	translation := &loopTranslation{guard: guard}
	for _, name := range order {
		translation.assigns = append(translation.assigns, fmt.Sprintf("{ var := %d, ty := %s, value := %s }", t.names[name], t.typeOf(name), assigned[name]))
	}
	translation.variables = t.variables
	return translation, ""
}

func (t *translator) fail(format string, args ...interface{}) string {
	if t.err == "" {
		t.err = fmt.Sprintf(format, args...)
	}
	return "sorry"
}

func (t *translator) index(name string) int {
	if i, ok := t.names[name]; ok {
		return i
	}
	t.names[name] = len(t.variables)
	t.variables = append(t.variables, name)
	return t.names[name]
}

// block executes statements sequentially, threading the symbolic state.
func (t *translator) block(block *ast.BlockStatement, state map[string]string, order *[]string, assigned map[string]string) {
	if block == nil {
		return
	}
	for _, stmt := range block.Statements {
		t.statement(stmt, state, order, assigned)
		if t.err != "" {
			return
		}
	}
}

// assign records a variable's new symbolic value. Later reads in the same
// iteration see the value as the program stored it, wrapped to the
// variable's representation (Oak.Loops.Expr.wrap); the emitted assignment
// carries the unwrapped expression, which Loop.step wraps.
func (t *translator) assign(name, value string, state map[string]string, order *[]string, assigned map[string]string) {
	ty := t.typeOf(name)
	if ty == "" {
		t.fail("the representation of `%s` is not evident (declare it with an integer or Bool type)", name)
		return
	}
	if _, seen := state[name]; !seen {
		*order = append(*order, name)
	}
	state[name] = fmt.Sprintf("(.wrap %s %s)", ty, value)
	assigned[name] = value
}

func (t *translator) statement(stmt ast.Statement, state map[string]string, order *[]string, assigned map[string]string) {
	switch s := stmt.(type) {
	case *ast.AssignmentStatement:
		if s.Name == nil {
			t.fail("an assignment without a target")
			return
		}
		t.index(s.Name.Value)
		t.assign(s.Name.Value, t.expr(s.Value, state), state, order, assigned)
	case *ast.ExpressionStatement:
		match, isMatch := s.Expression.(*ast.MatchExpression)
		if !isMatch {
			t.fail("the body contains a statement outside the fragment (%T)", s.Expression)
			return
		}
		t.conditional(match, state, order, assigned)
	case *ast.BlockStatement:
		t.block(s, state, order, assigned)
	case *ast.VariableDeclaration:
		t.fail("the body declares `%s`; loop-local declarations are outside the fragment", s.Name.Value)
	case *ast.WhileStatement:
		t.fail("the body contains a nested loop")
	default:
		t.fail("the body contains a statement outside the fragment (%T)", stmt)
	}
}

// conditional executes `c ? { A } | { B }`: both arms run from the current
// state and each assigned variable becomes cond(c, A-value, B-value).
func (t *translator) conditional(match *ast.MatchExpression, state map[string]string, order *[]string, assigned map[string]string) {
	arms := boolArms(match)
	if arms == nil {
		t.fail("the body contains a match that is not a Boolean conditional")
		return
	}
	condition := t.expr(match.Scrutinee, state)
	// Each arm runs from the current state; its unwrapped results are the
	// candidate values of the variables it assigns.
	branch := func(body ast.Expression) map[string]string {
		copy, results := map[string]string{}, map[string]string{}
		for k, v := range state {
			copy[k] = v
		}
		if body == nil {
			return results
		}
		block, isBlock := body.(*ast.BlockExpression)
		if !isBlock {
			t.fail("a conditional arm in statement position is not a block")
			return results
		}
		var local []string
		t.block(block.Block, copy, &local, results)
		return results
	}
	whenTrue, whenFalse := branch(arms[0]), branch(arms[1])
	if t.err != "" {
		return
	}
	names := map[string]bool{}
	for name := range whenTrue {
		names[name] = true
	}
	for name := range whenFalse {
		names[name] = true
	}
	sorted := make([]string, 0, len(names))
	for name := range names {
		sorted = append(sorted, name)
	}
	sort.Strings(sorted)
	for _, name := range sorted {
		// A variable one arm leaves alone keeps its current (already
		// wrapped) value; wrapping it again is the identity.
		before, had := state[name]
		if !had {
			before = fmt.Sprintf("(.var %d)", t.index(name))
		}
		yes, no := before, before
		if v, ok := whenTrue[name]; ok {
			yes = v
		}
		if v, ok := whenFalse[name]; ok {
			no = v
		}
		if yes == no {
			t.assign(name, yes, state, order, assigned)
			continue
		}
		t.assign(name, fmt.Sprintf("(.cond %s %s %s)", condition, yes, no), state, order, assigned)
	}
}

// boolArms returns the true and false arm bodies of a Boolean conditional
// (`c ? a | b` desugars to literal true/false arms), or nil.
func boolArms(match *ast.MatchExpression) []ast.Expression {
	if match == nil || len(match.Arms) != 2 {
		return nil
	}
	arms := make([]ast.Expression, 2)
	for _, arm := range match.Arms {
		literal, ok := arm.Pattern.(*ast.LiteralPattern)
		if !ok {
			return nil
		}
		boolean, ok := literal.Value.(*ast.Boolean)
		if !ok {
			return nil
		}
		if boolean.Value {
			arms[0] = arm.Body
		} else {
			arms[1] = arm.Body
		}
	}
	if arms[0] == nil && arms[1] == nil {
		return nil
	}
	return arms
}

var infixOps = map[string]string{
	"+": ".add", "-": ".sub", "*": ".mul", "/": ".div", "%": ".rem",
	"<": ".lt", "<=": ".le", ">": ".gt", ">=": ".ge", "==": ".eq", "!=": ".ne",
	"&&": ".and", "||": ".or",
}

// expr renders an expression; state supplies the symbolic value of
// variables assigned earlier in the body (nil for the guard).
func (t *translator) expr(expr ast.Expression, state map[string]string) string {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return literal(e.Value)
	case *ast.Boolean:
		if e.Value {
			return "(.lit 1)"
		}
		return "(.lit 0)"
	case *ast.Identifier:
		if strings.Contains(e.Value, ".") {
			return t.fail("`%s` is a qualified name; only locals are in the fragment", e.Value)
		}
		if state != nil {
			if value, assigned := state[e.Value]; assigned {
				return value
			}
		}
		return fmt.Sprintf("(.var %d)", t.index(e.Value))
	case *ast.InfixExpression:
		op, ok := infixOps[e.Operator]
		if !ok {
			return t.fail("operator `%s` is outside the fragment", e.Operator)
		}
		return fmt.Sprintf("(.bin %s %s %s)", op, t.expr(e.Left, state), t.expr(e.Right, state))
	case *ast.PrefixExpression:
		switch e.Operator {
		case "!":
			return fmt.Sprintf("(.not %s)", t.expr(e.Right, state))
		case "-":
			return fmt.Sprintf("(.neg %s)", t.expr(e.Right, state))
		}
		return t.fail("prefix operator `%s` is outside the fragment", e.Operator)
	case *ast.InvocationExpression:
		// T(literal) is the constant literal (docs/spec/25-type-inference.md
		// section 3a); any other call is outside the fragment.
		if name, ok := e.Function.(*ast.Identifier); ok && integerTypes[name.Value] != "" && len(e.Arguments) == 1 {
			if lit, ok := e.Arguments[0].(*ast.IntegerLiteral); ok {
				return literal(lit.Value)
			}
		}
		return t.fail("the loop calls a function; calls are outside the fragment")
	case *ast.MatchExpression:
		arms := boolArms(e)
		if arms == nil || arms[0] == nil || arms[1] == nil {
			return t.fail("a match that is not a two-armed Boolean conditional is outside the fragment")
		}
		return fmt.Sprintf("(.cond %s %s %s)", t.expr(e.Scrutinee, state), t.expr(arms[0], state), t.expr(arms[1], state))
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) == 1 {
			if inner, ok := e.Block.Statements[0].(*ast.ExpressionStatement); ok {
				return t.expr(inner.Expression, state)
			}
		}
		return t.fail("a block expression with statements is outside the fragment")
	}
	return t.fail("expression %T is outside the fragment", expr)
}

func literal(v int64) string {
	if v < 0 {
		return fmt.Sprintf("(.lit (%d))", v)
	}
	return fmt.Sprintf("(.lit %d)", v)
}

// integerTypes maps Oak integer type names to their Oak.Loops
// representation (platform-sized names at 64 bits).
var integerTypes = map[string]string{
	"u8": "(.u 8)", "u16": "(.u 16)", "u32": "(.u 32)", "u64": "(.u 64)",
	"i8": "(.s 8)", "i16": "(.s 16)", "i32": "(.s 32)", "i64": "(.s 64)",
	"uint": "(.u 64)", "uptr": "(.u 64)", "int": "(.s 64)", "byte": "(.u 8)", "rune": "(.s 32)",
}

// typeOf finds the declared representation of a variable: a parameter or
// local declaration with an integer or Bool annotation in the enclosing
// function, or an initializer whose representation is evident.
func (t *translator) typeOf(name string) string {
	if ty, done := t.types[name]; done {
		return ty
	}
	ty := ""
	var fn *ast.FunctionStatement
	for _, stmt := range t.program.Statements {
		if f, ok := stmt.(*ast.FunctionStatement); ok && f.Name != nil && f.Name.Value == t.function {
			fn = f
		}
	}
	if fn != nil {
		for _, parameter := range fn.Parameters {
			if parameter != nil && parameter.Name != nil && parameter.Name.Value == name {
				ty = leanType(parameter.Type)
			}
		}
		if ty == "" {
			forEachDeclaration(fn.Body, func(decl *ast.VariableDeclaration) {
				if decl.Name != nil && decl.Name.Value == name && ty == "" {
					ty = leanType(decl.Type)
					if ty == "" {
						ty = evidentType(decl.Value)
					}
				}
			})
		}
	}
	t.types[name] = ty
	return ty
}

func leanType(expr ast.Expression) string {
	id, ok := expr.(*ast.Identifier)
	if !ok {
		return ""
	}
	if id.Value == "Bool" {
		return ".b"
	}
	return integerTypes[id.Value]
}

// evidentType reads the representation off an initializer: a Boolean
// literal, a comparison, or a `T(literal)` constructor.
func evidentType(expr ast.Expression) string {
	switch e := expr.(type) {
	case *ast.Boolean:
		return ".b"
	case *ast.InfixExpression:
		switch e.Operator {
		case "<", "<=", ">", ">=", "==", "!=", "&&", "||":
			return ".b"
		}
	case *ast.InvocationExpression:
		if name, ok := e.Function.(*ast.Identifier); ok && len(e.Arguments) == 1 {
			return integerTypes[name.Value]
		}
	}
	return ""
}

// forEachDeclaration visits variable declarations under an expression
// (function bodies are block expressions).
func forEachDeclaration(expr ast.Expression, visit func(*ast.VariableDeclaration)) {
	var walkStmt func(ast.Statement)
	var walkExpr func(ast.Expression)
	walkStmt = func(stmt ast.Statement) {
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			visit(s)
		case *ast.WhileStatement:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.BlockStatement:
			for _, inner := range s.Statements {
				walkStmt(inner)
			}
		case *ast.UnsafeBlock:
			if s.Body != nil {
				for _, inner := range s.Body.Statements {
					walkStmt(inner)
				}
			}
		case *ast.ExpressionStatement:
			walkExpr(s.Expression)
		}
	}
	walkExpr = func(expr ast.Expression) {
		switch e := expr.(type) {
		case *ast.BlockExpression:
			if e.Block != nil {
				for _, inner := range e.Block.Statements {
					walkStmt(inner)
				}
			}
		case *ast.MatchExpression:
			for _, arm := range e.Arms {
				walkExpr(arm.Body)
			}
		}
	}
	walkExpr(expr)
}
