package prove

import (
	"crypto/sha256"
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

const synthesisPrefix = "oak_synth_"

// MaxSynthesisCandidates bounds search work, not the executions covered by an
// accepted inductive invariant. Every candidate is a pure scalar predicate.
const MaxSynthesisCandidates = 64

// SynthesisOptions controls the untrusted Houdini-style candidate search.
// Nil Candidates selects built-in templates; a non-nil empty slice selects none.
// Candidates use the original theorem's parameter names. They cannot introduce
// declarations, calls to user code, assumptions, or changes to the property.
type SynthesisOptions struct {
	Candidates []string
	Cases      int
	MaxRounds  int
}

// SynthesisCheck records the exact fresh obligation checked by the ordinary Go
// decider. A rejected preservation candidate is not a reachable counterexample.
type SynthesisCheck struct {
	Name   string `json:"name"`
	Status Status `json:"status"`
	Detail string `json:"detail"`
}

type SynthesisRejection struct {
	Predicate string         `json:"predicate"`
	Round     int            `json:"round"`
	Check     SynthesisCheck `json:"check"`
}

// SynthesisResult is an evidence report, not a certificate or a new authority
// level. Decided uses the existing interpreter/BDD trust boundary. It says
// nothing about the native executable, arbitrary system sizes, or liveness.
type SynthesisResult struct {
	Property     string               `json:"property"`
	Protocol     string               `json:"protocol"`
	SourceSHA256 string               `json:"source_sha256"`
	Status       Status               `json:"status"`
	Detail       string               `json:"detail"`
	Invariant    string               `json:"invariant,omitempty"`
	Retained     []string             `json:"retained"`
	Rejected     []SynthesisRejection `json:"rejected"`
	Checks       []SynthesisCheck     `json:"checks"`
	Rounds       int                  `json:"rounds"`
}

// SynthesizeInvariant searches conjunctions over a fixed, self-contained source
// snapshot. Only freshly checked initialization, preservation, and implication
// obligations authorize success. Reachability fallback and summary rows are not
// used: a failed induction step can be unreachable, and a bounded exploration
// cannot substitute for induction. This first implementation uses the Go ladder.
func SynthesizeInvariant(source compiler.SourceText, property string, options SynthesisOptions) (SynthesisResult, error) {
	report := SynthesisResult{
		Property: property, SourceSHA256: fmt.Sprintf("%x", sha256.Sum256([]byte(source.Text))),
		Status: Open, Retained: []string{}, Rejected: []SynthesisRejection{}, Checks: []SynthesisCheck{},
	}
	if options.Cases < 0 || options.MaxRounds < 0 {
		return report, fmt.Errorf("synthesis: budgets must be nonnegative")
	}
	if options.Cases == 0 {
		options.Cases = DefaultCases
	}
	comp := compiler.New().WithSource(source.Path, source.Text)
	tree, err := comp.Parse().Get()
	if err != nil {
		return report, err
	}
	// Imported source is not covered by this snapshot's digest. Refuse it before
	// checking/loading; future package support must bind the complete closure.
	var sourceErr error
	walkAST(tree.Root, func(node ast.Node) {
		switch n := node.(type) {
		case *ast.ImportStatement, *ast.ImportExpression:
			sourceErr = fmt.Errorf("synthesis: imports are not supported; use a self-contained source file")
		case *ast.Identifier:
			if strings.HasPrefix(n.Value, synthesisPrefix) {
				sourceErr = fmt.Errorf("synthesis: source uses reserved synthesis name %q", n.Value)
			}
		}
	})
	if sourceErr != nil {
		return report, sourceErr
	}
	decl := invariantCandidates(tree)[property]
	if decl == nil {
		return report, fmt.Errorf("synthesis: %q is not a protocol invariant theorem", property)
	}
	report.Protocol = decl.Name.Value
	var target *ast.FunctionStatement
	for _, stmt := range tree.Root.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil && fn.Name.Value == property {
			target = fn
		}
	}
	if target == nil || len(decl.Resources) != 0 {
		return report, fmt.Errorf("synthesis: only ordinary protocol invariant theorems are supported")
	}
	state := target.Parameters[0].Name.Value
	data := ""
	fields := map[string]string{}
	if decl.Data != nil {
		data = target.Parameters[1].Name.Value
		for _, field := range decl.Data.FieldOrder {
			typ, ok := field.Value.(*ast.Identifier)
			if !ok || !decidableFieldTypes[typ.Value] {
				return report, fmt.Errorf("synthesis: field %s must have a fixed-width integer or Bool type", field.Name)
			}
			fields[field.Name] = typ.Value
		}
	}
	if !synthesisPredicate(target.Body, state, data, fields) {
		return report, fmt.Errorf("synthesis: the original property must be a pure scalar predicate")
	}
	// A repeated (step, source state) needs a proof that all guards are disjoint.
	// An unguarded alternative is not covered by ProtocolGuardExclusivity.
	groups := map[string][]*ast.ProtocolTransition{}
	for _, line := range decl.Transitions {
		if line.Callable != nil {
			return report, fmt.Errorf("synthesis: via callables are outside the protocol projection scope")
		}
		key := line.Name.Value + "/" + line.From.Value
		groups[key] = append(groups[key], line)
	}
	expectedPairs := 0
	for key, lines := range groups {
		if len(lines) < 2 {
			continue
		}
		for _, line := range lines {
			if line.Guard == nil {
				report.Detail = "determinism not established: unguarded alternatives for " + key
				return report, nil
			}
		}
		expectedPairs += len(lines) * (len(lines) - 1) / 2
	}
	var exclusivity []string
	comp = comp.WithSyntaxRewrite(func(t *compiler.SyntaxTree) error {
		for _, stmt := range compiler.ProtocolGuardExclusivity(t) {
			fn, ok := stmt.(*ast.FunctionStatement)
			if ok && strings.Contains(fn.Name.Value, compiler.ExclusivityMarker+decl.Name.Value+"__") {
				t.Root.Statements = append(t.Root.Statements, stmt)
				exclusivity = append(exclusivity, fn.Name.Value)
			}
		}
		return nil
	})
	model, err := comp.Check().Get()
	if err != nil {
		return report, err
	}
	if len(exclusivity) != expectedPairs {
		return report, fmt.Errorf("synthesis: missing guard-exclusivity obligations")
	}
	checks, err := synthesisDecide(model, exclusivity, options.Cases)
	if err != nil {
		return report, err
	}
	report.Checks = append(report.Checks, checks...)
	for _, check := range checks {
		if check.Status != Decided {
			report.Detail = "determinism not established: " + check.Detail
			return report, nil
		}
	}
	// Subsequent checks rebuild from these same bytes. Exclusivity has already
	// been established for this snapshot and does not need to run every round.
	comp = compiler.New().WithSource(source.Path, source.Text)
	candidates := options.Candidates
	if candidates == nil {
		candidates = synthesisTemplates(decl, data, fields)
	}
	if len(candidates) > MaxSynthesisCandidates {
		return report, fmt.Errorf("synthesis: at most %d candidate predicates", MaxSynthesisCandidates)
	}
	var retained []string
	seen := map[string]bool{}
	for _, candidate := range candidates {
		expr, err := parseSynthesisPredicate(candidate)
		if err != nil || !synthesisPredicate(expr, state, data, fields) {
			return report, fmt.Errorf("synthesis: invalid candidate %q: expected one pure scalar predicate", candidate)
		}
		canonical := expr.String()
		if !seen[canonical] {
			retained = append(retained, canonical)
			seen[canonical] = true
		}
	}
	maxRounds := options.MaxRounds
	if maxRounds == 0 {
		maxRounds = len(retained) + 1
	}
	for round := 1; round <= maxRounds; round++ {
		report.Rounds = round
		generated, names := synthesisObligations(target, decl, retained)
		checked, err := comp.WithSyntaxRewrite(synthesisAppend(generated)).Check().Get()
		if err != nil {
			return report, fmt.Errorf("synthesis: check candidate obligations: %w", err)
		}
		// Every candidate must hold initially and be preserved under the whole
		// current conjunction. Remove unsupported as well as refuted candidates;
		// this loses search power but cannot authorize a false result.
		candidateChecks, err := synthesisDecide(checked, names[3:], options.Cases)
		if err != nil {
			return report, err
		}
		var next []string
		for i, predicate := range retained {
			base, step := candidateChecks[2*i], candidateChecks[2*i+1]
			failed := base
			if base.Status == Decided {
				failed = step
			}
			if failed.Status != Decided {
				report.Rejected = append(report.Rejected, SynthesisRejection{Predicate: predicate, Round: round, Check: failed})
			} else {
				next = append(next, predicate)
			}
		}
		if len(next) != len(retained) {
			retained = next
			continue // The hypothesis weakened: all remaining checks must rerun.
		}
		// Do not infer success from the search's cached candidate results.
		// Check the complete final invariant and its implication afresh.
		final, err := synthesisDecide(checked, names[:3], options.Cases)
		if err != nil {
			return report, err
		}
		report.Checks = append(report.Checks, final...)
		report.Retained = append(report.Retained, retained...)
		for _, check := range final {
			if check.Status != Decided {
				report.Detail = "no inductive strengthening established: " + check.Name + ": " + check.Detail
				return report, nil
			}
		}
		report.Status = Decided
		report.Invariant = synthesisConjunction(target, retained)
		report.Detail = "initialization, preservation, and original-property implication decided; arbitrary transition count for the declared deterministic protocol projection and types; not liveness or executable refinement"
		return report, nil
	}
	report.Detail = "candidate-search round budget exhausted; no invariant accepted"
	return report, nil
}

func parseSynthesisPredicate(text string) (ast.Expression, error) {
	if len(text) == 0 || len(text) > 4096 {
		return nil, fmt.Errorf("candidate must contain 1..4096 bytes")
	}
	p := parser.New(layout.New(scanner.New(text)))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 || len(program.Statements) != 1 {
		return nil, fmt.Errorf("expected exactly one expression")
	}
	stmt, ok := program.Statements[0].(*ast.ExpressionStatement)
	if !ok || stmt.Discard {
		return nil, fmt.Errorf("expected a predicate expression")
	}
	return stmt.Expression, nil
}

// This whitelist is deliberately syntactic. Type checking still decides the
// predicate's types. In particular calls only admit built-in integer casts;
// candidates cannot call a theorem, synth helper, assumption, or user function.
func synthesisPredicate(expr ast.Expression, state, data string, fields map[string]string) bool {
	valid := func(e ast.Expression) bool { return synthesisPredicate(e, state, data, fields) }
	switch e := expr.(type) {
	case *ast.Boolean, *ast.IntegerLiteral:
		return true
	case *ast.Identifier:
		return e.Value == state
	case *ast.VariantExpression:
		return e.TypeName == nil && e.Payload == nil && e.Variant != nil
	case *ast.IndexExpression:
		base, ok := e.Left.(*ast.Identifier)
		field, fieldOK := e.Index.(*ast.Identifier)
		return ok && fieldOK && e.Dot && data != "" && base.Value == data && fields[field.Value] != ""
	case *ast.PrefixExpression:
		return (e.Operator == "!" || e.Operator == "-" || e.Operator == "~") && valid(e.Right)
	case *ast.InfixExpression:
		switch e.Operator {
		case "&&", "||", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>":
			return valid(e.Left) && valid(e.Right)
		}
	case *ast.InvocationExpression:
		name, ok := e.Function.(*ast.Identifier)
		return ok && name.Value != "Bool" && decidableFieldTypes[name.Value] && len(e.Arguments) == 1 && valid(e.Arguments[0])
	case *ast.BlockExpression:
		if e.Block != nil && e.Block.Order == "" && e.Block.DeferredFrom == 0 && len(e.Block.Statements) == 1 {
			stmt, ok := e.Block.Statements[0].(*ast.ExpressionStatement)
			return ok && !stmt.Discard && valid(stmt.Expression)
		}
	}
	return false
}

// Stable templates cover equality/order relations between same-typed fields,
// and equality/order against literal initial values. These guesses carry no
// authority; overflow-sensitive relations are checked with Oak's arithmetic.
func synthesisTemplates(decl *ast.ProtocolDeclaration, data string, fields map[string]string) []string {
	var candidates []string
	add := func(s string) {
		if len(candidates) < MaxSynthesisCandidates {
			candidates = append(candidates, s)
		}
	}
	if decl.Data == nil {
		return candidates
	}
	for i, a := range decl.Data.FieldOrder {
		for _, b := range decl.Data.FieldOrder[i+1:] {
			if fields[a.Name] != fields[b.Name] {
				continue
			}
			for _, op := range []string{"==", "<=", ">="} {
				if fields[a.Name] == "Bool" && op != "==" {
					continue
				}
				add(data + "." + a.Name + " " + op + " " + data + "." + b.Name)
			}
		}
	}
	if decl.Init != nil {
		for _, field := range decl.Init.FieldOrder {
			// A predicate with no state/data identifiers admits only constants.
			if !synthesisPredicate(field.Value, "", "", nil) {
				continue
			}
			for _, op := range []string{"==", "<=", ">="} {
				if fields[field.Name] == "Bool" && op != "==" {
					continue
				}
				add(data + "." + field.Name + " " + op + " " + field.Value.String())
			}
		}
	}
	return candidates
}

func synthesisSignature(target *ast.FunctionStatement) (string, string) {
	var params, args []string
	for _, p := range target.Parameters {
		params = append(params, p.String())
		args = append(args, p.Name.Value)
	}
	return strings.Join(params, ", "), strings.Join(args, ", ")
}

func synthesisConjunction(target *ast.FunctionStatement, predicates []string) string {
	_, args := synthesisSignature(target)
	terms := []string{target.Name.Value + "(" + args + ")"}
	for _, predicate := range predicates {
		terms = append(terms, "("+predicate+")")
	}
	return strings.Join(terms, " && ")
}

func synthesisObligations(target *ast.FunctionStatement, decl *ast.ProtocolDeclaration, predicates []string) (string, []string) {
	params, args := synthesisSignature(target)
	state := target.Parameters[0].Name.Value
	prefix := compiler.ProtocolPrefix(decl.Name.Value)
	inv := synthesisPrefix + "invariant"
	var out strings.Builder
	fmt.Fprintf(&out, "%s: (%s): Bool = %s\n", inv, params, synthesisConjunction(target, predicates))
	initial := prefix + "_initial()"
	legal := prefix + "_legal(" + args + ", oak_synth_action)"
	stepParams := params + ", oak_synth_action: " + decl.Name.Value + "Step"
	next := prefix + "_next(" + state + ", oak_synth_action)"
	setup := ""
	if decl.Data != nil {
		initial += ", " + prefix + "_initial_data()"
		data := target.Parameters[1].Name.Value
		setup = fmt.Sprintf("oak_synth_buffer: [1]%sData = [1]%sData{ %s }\n", decl.Name.Value, decl.Name.Value, data)
		next = prefix + "_next(" + state + ", span(&oak_synth_buffer), oak_synth_action), oak_synth_buffer[0]"
	}
	baseName, stepName, implication := synthesisPrefix+"base", synthesisPrefix+"step", synthesisPrefix+"implies"
	names := []string{baseName, stepName, implication}
	writeBase := func(name, predicate string) {
		fmt.Fprintf(&out, "%s: theorem () = %s(%s)\n", name, predicate, initial)
	}
	writeStep := func(name, predicate string) {
		fmt.Fprintf(&out, "%s: theorem (%s) {\n%s!(%s(%s) && %s) || %s(%s)\n}\n", name, stepParams, setup, inv, args, legal, predicate, next)
	}
	writeBase(baseName, inv)
	writeStep(stepName, inv)
	// The extra Bool parameter prevents this universal implication from being
	// mistaken for a protocol invariant by callers of the general proof ladder.
	fmt.Fprintf(&out, "%s: theorem (%s, oak_synth_unused: Bool) = !%s(%s) || %s(%s)\n", implication, params, inv, args, target.Name.Value, args)
	for i, predicate := range predicates {
		fn := fmt.Sprintf("%scandidate_%d", synthesisPrefix, i)
		base, step := fn+"_base", fn+"_step"
		fmt.Fprintf(&out, "%s: (%s): Bool = %s\n", fn, params, predicate)
		writeBase(base, fn)
		writeStep(step, fn)
		names = append(names, base, step)
	}
	return out.String(), names
}

func synthesisAppend(source string) func(*compiler.SyntaxTree) error {
	return func(tree *compiler.SyntaxTree) error {
		p := parser.New(layout.New(scanner.New(source)))
		program := p.ParseProgram()
		if errs := p.Errors(); len(errs) != 0 {
			return fmt.Errorf("synthesis: generated obligations: %s", strings.Join(errs, "; "))
		}
		tree.Root.Statements = append(tree.Root.Statements, program.Statements...)
		return nil
	}
}

func synthesisDecide(model *compiler.SemanticModel, names []string, cases int) ([]SynthesisCheck, error) {
	if len(names) == 0 {
		return nil, nil
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if evaluated := evaluator.Eval(model.Tree.Root, env); evaluated != nil {
		if e, ok := evaluated.(*object.Error); ok {
			return nil, fmt.Errorf("synthesis: loading checked source: %s", e.Message)
		}
	}
	functions := map[string]*ast.FunctionStatement{}
	for _, stmt := range model.Tree.Root.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil {
			functions[fn.Name.Value] = fn
		}
	}
	decls := declarationsOf(model.Tree.Root, model.TypeChecker)
	checks := make([]SynthesisCheck, 0, len(names))
	for _, name := range names {
		fn := functions[name]
		if fn == nil || !fn.Theorem {
			return nil, fmt.Errorf("synthesis: missing theorem %q", name)
		}
		r := decide(env, model.TypeChecker, functions, decls, fn, cases, false)
		checks = append(checks, SynthesisCheck{Name: name, Status: r.Status, Detail: r.Detail})
	}
	return checks, nil
}
