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
		fmt.Fprintf(&out, "-- variables: %s\n", legend(translation.variables))
		if len(translation.arrays) != 0 {
			fmt.Fprintf(&out, "-- arrays: %s\n", legend(translation.arrays))
		}
		if len(translation.functions) != 0 {
			fmt.Fprintf(&out, "-- uninterpreted functions (constrain F with hypotheses): %s\n", legend(translation.functions))
		}
		fmt.Fprintf(&out, "def %s : Oak.Loops.Loop :=\n  { guard := %s,\n    body := [%s],\n    writes := [%s] }\n\n", name, translation.guard, strings.Join(translation.assigns, ",\n            "), strings.Join(translation.writes, ",\n              "))
		fmt.Fprintf(&out, "theorem %s_terminates : ∀ (F : Oak.Loops.Funs) (s : Oak.Loops.State), Oak.Loops.Terminates F %s s := by\n", name, name)
		fmt.Fprintf(&out, "  -- Discharge: intro F; exact Oak.Loops.ranking_terminates F %s (fun s => <rank>) (by intro s h; <decrease>)\n", name)
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
	writes    []string
	variables []string // variable index -> source name
	arrays    []string // array index -> source name
	functions []string // uninterpreted function index -> source name
}

func legend(names []string) string {
	parts := make([]string, 0, len(names))
	for i, name := range names {
		parts = append(parts, fmt.Sprintf("%d ↦ `%s`", i, modules.DemangleText(name)))
	}
	return strings.Join(parts, ", ")
}

// translator symbolically executes a loop body over the fragment Oak.Loops
// models. Variables and arrays are indices; the symbolic state maps each
// assigned variable to the Lean expression of its value in terms of the
// pre-iteration state, and each written array to its pending writes.
type translator struct {
	program   *ast.Program
	function  string
	names     map[string]int
	variables []string
	arrayIDs  map[string]int
	arrays    []string
	funcIDs   map[string]int
	functions []string
	types     map[string]string // Lean Ty per variable, "" unknown
	elements  map[string]string // Lean Ty per array element, "" unknown
	inlining  map[string]bool   // callees on the inlining stack
	err       string
}

// symbolicState is the in-iteration view: variable values as the program
// stored them (wrapped), loop-local declarations, and pending array writes
// in program order.
type symbolicState struct {
	vars   map[string]string
	locals map[string]string // loop-local declaration -> Lean type
	writes map[string][]pendingWrite
}

type pendingWrite struct {
	index, value, ty string
}

func newSymbolicState() *symbolicState {
	return &symbolicState{vars: map[string]string{}, locals: map[string]string{}, writes: map[string][]pendingWrite{}}
}

func (st *symbolicState) clone() *symbolicState {
	copy := newSymbolicState()
	for k, v := range st.vars {
		copy.vars[k] = v
	}
	for k, v := range st.locals {
		copy.locals[k] = v
	}
	for k, v := range st.writes {
		copy.writes[k] = append([]pendingWrite(nil), v...)
	}
	return copy
}

// results collects what a body (or an arm) assigned: the unwrapped final
// value of each variable in order, and the writes it performed.
type results struct {
	order    []string
	assigned map[string]string
	writes   []string
}

func newResults() *results { return &results{assigned: map[string]string{}} }

// translateLoop returns the translation or the reason none exists.
func translateLoop(loop *ast.WhileStatement, function string, program *ast.Program) (*loopTranslation, string) {
	t := &translator{program: program, function: function, names: map[string]int{}, arrayIDs: map[string]int{}, funcIDs: map[string]int{}, types: map[string]string{}, elements: map[string]string{}, inlining: map[string]bool{}}
	guard, _ := t.expr(loop.Condition, newSymbolicState())
	if t.err != "" {
		return nil, t.err
	}
	state, out := newSymbolicState(), newResults()
	t.block(loop.Body, state, out)
	if t.err != "" {
		return nil, t.err
	}
	translation := &loopTranslation{guard: guard, writes: out.writes}
	for _, name := range out.order {
		translation.assigns = append(translation.assigns, fmt.Sprintf("{ var := %d, ty := %s, value := %s }", t.names[name], t.typeOf(name), out.assigned[name]))
	}
	translation.variables, translation.arrays, translation.functions = t.variables, t.arrays, t.functions
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

func (t *translator) arrayIndex(name string) int {
	if i, ok := t.arrayIDs[name]; ok {
		return i
	}
	t.arrayIDs[name] = len(t.arrays)
	t.arrays = append(t.arrays, name)
	return t.arrayIDs[name]
}

func (t *translator) functionIndex(name string) int {
	if i, ok := t.funcIDs[name]; ok {
		return i
	}
	t.funcIDs[name] = len(t.functions)
	t.functions = append(t.functions, name)
	return t.funcIDs[name]
}

// block executes statements sequentially, threading the symbolic state.
func (t *translator) block(block *ast.BlockStatement, state *symbolicState, out *results) {
	if block == nil {
		return
	}
	for _, stmt := range block.Statements {
		t.statement(stmt, state, out)
		if t.err != "" {
			return
		}
	}
}

// assign records a variable's new symbolic value. Later reads in the same
// iteration see the value as the program stored it, wrapped to the
// variable's representation; the emitted assignment carries the unwrapped
// expression, which Loop.step wraps.
func (t *translator) assign(name, value string, state *symbolicState, out *results) {
	if _, local := state.locals[name]; local {
		t.fail("the loop-local `%s` is reassigned; loop-local declarations are single-assignment in the fragment", name)
		return
	}
	ty := t.typeOf(name)
	if ty == "" {
		t.fail("the representation of `%s` is not evident (declare it with an integer or Bool type)", name)
		return
	}
	if _, seen := out.assigned[name]; !seen {
		out.order = append(out.order, name)
	}
	state.vars[name] = fmt.Sprintf("(.wrap %s %s)", ty, value)
	out.assigned[name] = value
}

func (t *translator) statement(stmt ast.Statement, state *symbolicState, out *results) {
	switch s := stmt.(type) {
	case *ast.AssignmentStatement:
		if s.Name == nil {
			t.fail("an assignment without a target")
			return
		}
		t.index(s.Name.Value)
		value, _ := t.expr(s.Value, state)
		t.assign(s.Name.Value, value, state, out)
	case *ast.VariableDeclaration:
		// A loop-local declaration is substituted where it is read; it is
		// never part of the loop's state.
		if s.Name == nil {
			t.fail("a declaration without a name")
			return
		}
		value, inferred := t.expr(s.Value, state)
		ty := leanType(s.Type)
		if ty == "" {
			ty = inferred
		}
		if ty == "" {
			t.fail("the representation of the loop-local `%s` is not evident (annotate it)", s.Name.Value)
			return
		}
		state.locals[s.Name.Value] = ty
		state.vars[s.Name.Value] = fmt.Sprintf("(.wrap %s %s)", ty, value)
	case *ast.IndexAssignmentStatement:
		t.store(s, state, out)
	case *ast.ExpressionStatement:
		match, isMatch := s.Expression.(*ast.MatchExpression)
		if !isMatch {
			t.fail("the body contains a statement outside the fragment (%T)", s.Expression)
			return
		}
		t.conditional(match, state, out)
	case *ast.BlockStatement:
		t.block(s, state, out)
	case *ast.WhileStatement:
		t.fail("the body contains a nested loop")
	default:
		t.fail("the body contains a statement outside the fragment (%T)", stmt)
	}
}

// store executes `arr[index] = value`: the write joins the iteration's
// writes, and later reads of the array in the same iteration see it.
func (t *translator) store(s *ast.IndexAssignmentStatement, state *symbolicState, out *results) {
	if s.Target == nil || s.Target.Dot {
		t.fail("the body assigns through a field access; only array element stores are in the fragment")
		return
	}
	array, ok := s.Target.Left.(*ast.Identifier)
	if !ok {
		t.fail("the body stores into an expression that is not an array variable")
		return
	}
	ty := t.elementType(array.Value)
	if ty == "" {
		t.fail("the element representation of `%s` is not evident (declare it as [N]T with an integer or Bool element type)", array.Value)
		return
	}
	id := t.arrayIndex(array.Value)
	index, _ := t.expr(s.Target.Index, state)
	value, _ := t.expr(s.Value, state)
	if t.err != "" {
		return
	}
	write := pendingWrite{index: index, value: value, ty: ty}
	state.writes[array.Value] = append(state.writes[array.Value], write)
	out.writes = append(out.writes, fmt.Sprintf("{ arr := %d, ty := %s, index := %s, value := %s }", id, ty, index, value))
}

// conditional executes `c ? { A } | { B }`: both arms run from the current
// state; each assigned variable becomes cond(c, A-value, B-value) and each
// arm's writes are conditioned on c (a write the arm does not perform is a
// write of the cell's own value).
func (t *translator) conditional(match *ast.MatchExpression, state *symbolicState, out *results) {
	arms := boolArms(match)
	if arms == nil {
		t.fail("the body contains a match that is not a Boolean conditional")
		return
	}
	condition, _ := t.expr(match.Scrutinee, state)
	branch := func(body ast.Expression) (*symbolicState, *results) {
		copy, results := state.clone(), newResults()
		if body == nil {
			return copy, results
		}
		block, isBlock := body.(*ast.BlockExpression)
		if !isBlock {
			t.fail("a conditional arm in statement position is not a block")
			return copy, results
		}
		t.block(block.Block, copy, results)
		return copy, results
	}
	yesState, yes := branch(arms[0])
	noState, no := branch(arms[1])
	if t.err != "" {
		return
	}
	names := map[string]bool{}
	for name := range yes.assigned {
		names[name] = true
	}
	for name := range no.assigned {
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
		before, had := state.vars[name]
		if !had {
			before = fmt.Sprintf("(.var %d)", t.index(name))
		}
		whenTrue, whenFalse := before, before
		if v, ok := yes.assigned[name]; ok {
			whenTrue = v
		}
		if v, ok := no.assigned[name]; ok {
			whenFalse = v
		}
		if whenTrue == whenFalse {
			t.assign(name, whenTrue, state, out)
			continue
		}
		t.assign(name, fmt.Sprintf("(.cond %s %s %s)", condition, whenTrue, whenFalse), state, out)
	}
	// Writes: an arm's writes happen only when its condition holds. A write
	// under a false condition stores the cell's current value back, which
	// is the identity on memory.
	conditionWrites := func(from *symbolicState, guardTrue bool, arm *results) {
		for _, write := range arm.writes {
			_ = write
		}
		for array, pending := range from.writes {
			already := len(state.writes[array])
			for _, w := range pending[already:] {
				cell := fmt.Sprintf("(.index %d %s)", t.arrayIndex(array), w.index)
				value := fmt.Sprintf("(.cond %s %s %s)", condition, w.value, cell)
				if !guardTrue {
					value = fmt.Sprintf("(.cond %s %s %s)", condition, cell, w.value)
				}
				state.writes[array] = append(state.writes[array], pendingWrite{index: w.index, value: value, ty: w.ty})
				out.writes = append(out.writes, fmt.Sprintf("{ arr := %d, ty := %s, index := %s, value := %s }", t.arrayIndex(array), w.ty, w.index, value))
			}
		}
	}
	conditionWrites(yesState, true, yes)
	conditionWrites(noState, false, no)
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

var arithmeticOps = map[string]string{"+": ".add", "-": ".sub", "*": ".mul", "/": ".div", "%": ".rem"}

var comparisonOps = map[string]string{
	"<": ".lt", "<=": ".le", ">": ".gt", ">=": ".ge", "==": ".eq", "!=": ".ne",
	"&&": ".and", "||": ".or",
}

// expr renders an expression and its representation ("" when not evident);
// state supplies the symbolic value of variables assigned earlier in the
// body and the pending writes reads must see. Arithmetic wraps to its
// representation, as Oak's total fixed-width arithmetic does.
func (t *translator) expr(expr ast.Expression, state *symbolicState) (string, string) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return literal(e.Value), ""
	case *ast.Boolean:
		if e.Value {
			return "(.lit 1)", ".b"
		}
		return "(.lit 0)", ".b"
	case *ast.Identifier:
		if strings.Contains(e.Value, ".") {
			return t.fail("`%s` is a qualified name; only locals are in the fragment", e.Value), ""
		}
		if ty, local := state.locals[e.Value]; local {
			return state.vars[e.Value], ty
		}
		if value, assigned := state.vars[e.Value]; assigned {
			return value, t.typeOf(e.Value)
		}
		return fmt.Sprintf("(.var %d)", t.index(e.Value)), t.typeOf(e.Value)
	case *ast.InfixExpression:
		left, leftTy := t.expr(e.Left, state)
		right, rightTy := t.expr(e.Right, state)
		if op, ok := arithmeticOps[e.Operator]; ok {
			ty := leftTy
			if ty == "" {
				ty = rightTy
			}
			if ty == "" {
				return t.fail("the representation of `%s` is not evident", e.String()), ""
			}
			return fmt.Sprintf("(.wrap %s (.bin %s %s %s))", ty, op, left, right), ty
		}
		if op, ok := comparisonOps[e.Operator]; ok {
			return fmt.Sprintf("(.bin %s %s %s)", op, left, right), ".b"
		}
		return t.fail("operator `%s` is outside the fragment", e.Operator), ""
	case *ast.PrefixExpression:
		operand, ty := t.expr(e.Right, state)
		switch e.Operator {
		case "!":
			return fmt.Sprintf("(.not %s)", operand), ".b"
		case "-":
			if ty == "" {
				return t.fail("the representation of `%s` is not evident", e.String()), ""
			}
			return fmt.Sprintf("(.wrap %s (.neg %s))", ty, operand), ty
		}
		return t.fail("prefix operator `%s` is outside the fragment", e.Operator), ""
	case *ast.IndexExpression:
		if e.Dot {
			return t.fail("field access `%s` is outside the fragment", e.String()), ""
		}
		array, ok := e.Left.(*ast.Identifier)
		if !ok {
			return t.fail("indexing an expression that is not an array variable is outside the fragment"), ""
		}
		ty := t.elementType(array.Value)
		if ty == "" {
			return t.fail("the element representation of `%s` is not evident", array.Value), ""
		}
		index, _ := t.expr(e.Index, state)
		return t.read(array.Value, index, state), ty
	case *ast.InvocationExpression:
		return t.call(e, state)
	case *ast.MatchExpression:
		arms := boolArms(e)
		if arms == nil || arms[0] == nil || arms[1] == nil {
			return t.fail("a match that is not a two-armed Boolean conditional is outside the fragment"), ""
		}
		condition, _ := t.expr(e.Scrutinee, state)
		yes, yesTy := t.expr(arms[0], state)
		no, noTy := t.expr(arms[1], state)
		ty := yesTy
		if ty == "" {
			ty = noTy
		}
		return fmt.Sprintf("(.cond %s %s %s)", condition, yes, no), ty
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) == 1 {
			if inner, ok := e.Block.Statements[0].(*ast.ExpressionStatement); ok {
				return t.expr(inner.Expression, state)
			}
		}
		return t.fail("a block expression with statements is outside the fragment"), ""
	}
	return t.fail("expression %T is outside the fragment", expr), ""
}

// read renders `arr[index]` seeing the iteration's pending writes to the
// array, latest first.
func (t *translator) read(array, index string, state *symbolicState) string {
	value := fmt.Sprintf("(.index %d %s)", t.arrayIndex(array), index)
	pending := state.writes[array]
	for i := len(pending) - 1; i >= 0; i-- {
		w := pending[i]
		value = fmt.Sprintf("(.cond (.bin .eq %s %s) (.wrap %s %s) %s)", index, w.index, w.ty, w.value, value)
	}
	return value
}

// call renders a call: `T(literal)` is the constant; an expression-bodied,
// non-recursive, non-generic function of the program whose body is in the
// fragment is inlined with its arguments substituted; any other callee is
// an uninterpreted function of the statement.
func (t *translator) call(e *ast.InvocationExpression, state *symbolicState) (string, string) {
	name, ok := e.Function.(*ast.Identifier)
	if !ok {
		return t.fail("calling an expression that is not a function name is outside the fragment"), ""
	}
	if ty := integerTypes[name.Value]; ty != "" && len(e.Arguments) == 1 {
		// An integer conversion: the value at the target representation.
		if lit, ok := e.Arguments[0].(*ast.IntegerLiteral); ok {
			return literal(lit.Value), ty
		}
		operand, _ := t.expr(e.Arguments[0], state)
		return fmt.Sprintf("(.wrap %s %s)", ty, operand), ty
	}
	// Explicit narrowing (docs/spec/20-types.md section 11.1): `T_trunc_S(x)`
	// wraps to T and `T_bits_S(x)` reinterprets same-width bits, which is
	// the same wrap in two's complement; saturating and checked forms are
	// outside the fragment.
	if target, ok := conversionTarget(name.Value); ok && len(e.Arguments) == 1 {
		operand, _ := t.expr(e.Arguments[0], state)
		return fmt.Sprintf("(.wrap %s %s)", target, operand), target
	}
	if name.Value == "Bool" && len(e.Arguments) == 1 {
		operand, _ := t.expr(e.Arguments[0], state)
		return fmt.Sprintf("(.wrap .b %s)", operand), ".b"
	}
	callee := t.functionNamed(name.Value)
	if callee == nil {
		return t.fail("`%s` is not a function of the program", name.Value), ""
	}
	if len(callee.Parameters) != len(e.Arguments) {
		return t.fail("call to `%s` passes %d arguments for %d parameters", name.Value, len(e.Arguments), len(callee.Parameters)), ""
	}
	args := make([]string, 0, len(e.Arguments))
	for _, argument := range e.Arguments {
		value, _ := t.expr(argument, state)
		args = append(args, value)
	}
	if t.err != "" {
		return "sorry", ""
	}
	returnTy := leanType(callee.ReturnType)
	if inlined, ok := t.inline(callee, args); ok {
		return inlined, returnTy
	}
	if returnTy == "" {
		return t.fail("the result representation of `%s` is not evident", name.Value), ""
	}
	return fmt.Sprintf("(.call %d [%s])", t.functionIndex(name.Value), strings.Join(args, ", ")), returnTy
}

// conversionTarget recognizes `T_trunc_S` and `T_bits_S` and returns T's
// representation.
func conversionTarget(name string) (string, bool) {
	for _, op := range []string{"_trunc_", "_bits_"} {
		if i := strings.Index(name, op); i > 0 {
			target, source := name[:i], name[i+len(op):]
			if integerTypes[target] != "" && integerTypes[source] != "" {
				return integerTypes[target], true
			}
		}
	}
	return "", false
}

// inline substitutes the arguments into an expression-bodied callee whose
// body is in the fragment. Recursion and generics are not inlined.
func (t *translator) inline(callee *ast.FunctionStatement, args []string) (string, bool) {
	if callee.Name == nil || callee.Receiver != nil || len(callee.TypeParams) != 0 || t.inlining[callee.Name.Value] {
		return "", false
	}
	body := callee.Body
	if block, isBlock := body.(*ast.BlockExpression); isBlock {
		if block.Block == nil || len(block.Block.Statements) != 1 {
			return "", false
		}
		inner, ok := block.Block.Statements[0].(*ast.ExpressionStatement)
		if !ok {
			return "", false
		}
		body = inner.Expression
	}
	// Parameters are loop-locals of the callee's own scope.
	scope := newSymbolicState()
	for i, parameter := range callee.Parameters {
		if parameter == nil || parameter.Name == nil {
			return "", false
		}
		ty := leanType(parameter.Type)
		if ty == "" {
			return "", false
		}
		scope.locals[parameter.Name.Value] = ty
		scope.vars[parameter.Name.Value] = args[i]
	}
	saved := t.err
	t.inlining[callee.Name.Value] = true
	value, _ := t.expr(body, scope)
	delete(t.inlining, callee.Name.Value)
	if t.err != saved {
		// The body left the fragment: fall back to an uninterpreted call.
		t.err = saved
		return "", false
	}
	return value, true
}

func (t *translator) functionNamed(name string) *ast.FunctionStatement {
	for _, stmt := range t.program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil && fn.Name.Value == name {
			return fn
		}
	}
	return nil
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
	if fn := t.functionNamed(t.function); fn != nil {
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

// elementType finds the element representation of an array variable from
// its `[N]T` (or `[]T`, `[*]T`) declaration in the enclosing function.
func (t *translator) elementType(name string) string {
	if ty, done := t.elements[name]; done {
		return ty
	}
	ty := ""
	if fn := t.functionNamed(t.function); fn != nil {
		for _, parameter := range fn.Parameters {
			if parameter != nil && parameter.Name != nil && parameter.Name.Value == name {
				ty = elementLeanType(parameter.Type)
			}
		}
		if ty == "" {
			forEachDeclaration(fn.Body, func(decl *ast.VariableDeclaration) {
				if decl.Name != nil && decl.Name.Value == name && ty == "" {
					ty = elementLeanType(decl.Type)
				}
			})
		}
	}
	t.elements[name] = ty
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

// elementLeanType reads the element representation off an array type: the
// parser spells `[N]T` as an index of the element type by the length.
func elementLeanType(expr ast.Expression) string {
	switch e := expr.(type) {
	case *ast.IndexExpression:
		return leanType(e.Left)
	case *ast.PrefixExpression:
		return elementLeanType(e.Right)
	}
	return ""
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
