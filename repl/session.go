package repl

// Module-aware REPL sessions (docs/spec/83-modules.md section 10). A session
// is an in-memory root package compiled through the same pipeline as a
// build: imports resolve through the module enclosing the working directory
// (`oak.mod`), every input is checked by the type, borrow, and discipline
// gates, and expressions are evaluated by the tree-walking evaluator over the
// elaborated program. The REPL therefore sees packages, `pub`, sealed
// imports, and derived declarations exactly as the compiler does; it never
// invents a second module system.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// resultBinding is the top-level binding the session wraps an expression in
// so the checker types it and the evaluator produces it.
const resultBinding = "oak_repl_value"

// Session accumulates imports and declarations and evaluates expressions
// against them.
type Session struct {
	// ModuleDir is the directory whose enclosing oak.mod resolves imports
	// (the working directory by default).
	ModuleDir string
	IntSize   int
	PtrSize   int
	// Strict checks the session under the strict discipline profile, where
	// every recorded assumption is a rejection (docs/spec/85-discipline.md).
	Strict bool

	imports      []string
	declarations []string
}

// NewSession starts an empty session rooted at moduleDir.
func NewSession(moduleDir string) *Session {
	return &Session{ModuleDir: moduleDir, IntSize: 64, PtrSize: 64}
}

// Reset forgets every import and declaration.
func (s *Session) Reset() {
	s.imports, s.declarations = nil, nil
}

// Outcome is what one input produced.
type Outcome struct {
	// Value is the evaluated expression, nil for declarations and imports.
	Value object.Object
	// Type is the checked type of the expression (or of the declaration's
	// binding when it has one).
	Type typechecker.Type
	// Committed reports whether the input was added to the session.
	Committed bool
}

// Submit checks one input against the session. An input is import
// statements, declarations, or declarations followed by one trailing
// expression (or a lone expression). Imports and declarations that pass every
// gate join the session; the expression is checked, evaluated, and reported
// without being kept.
func (s *Session) Submit(input string) (Outcome, error) {
	program, err := parseInput(input)
	if err != nil {
		return Outcome{}, err
	}
	if len(program.Statements) == 0 {
		return Outcome{}, nil
	}
	var imports, declarations []string
	expression := ""
	last := program.Statements[len(program.Statements)-1]
	prefix := input
	if exprStmt, isExpr := last.(*ast.ExpressionStatement); isExpr {
		start := exprStmt.Token.ByteStart
		if start < 0 || start > len(input) {
			return Outcome{}, fmt.Errorf("cannot locate the expression in the input")
		}
		expression = strings.TrimSpace(input[start:])
		prefix = input[:start]
	}
	importCount, declarationCount := 0, 0
	for _, stmt := range program.Statements {
		switch stmt.(type) {
		case *ast.ImportStatement:
			importCount++
		case *ast.ExpressionStatement:
		default:
			declarationCount++
		}
	}
	if importCount != 0 && declarationCount != 0 {
		return Outcome{}, fmt.Errorf("submit imports and declarations as separate inputs")
	}
	if text := strings.TrimSpace(prefix); text != "" {
		if importCount != 0 {
			imports = append(imports, text)
		} else {
			declarations = append(declarations, text)
		}
	}
	source := s.compose(imports, declarations, expression)
	// The strict profile judges declarations; an expression's wrapper
	// binding is runtime-initialized by construction and is checked in the
	// default profile.
	model, err := s.compileWith(source, s.Strict && expression == "")
	if err != nil {
		return Outcome{}, err
	}
	outcome := Outcome{}
	if expression == "" {
		s.imports = append(s.imports, imports...)
		s.declarations = append(s.declarations, declarations...)
		outcome.Committed = true
		if name := declarationBinding(last); name != "" {
			if scheme, ok := model.TypeChecker.Env().Get(name); ok && scheme != nil {
				outcome.Type = scheme.Type
			}
		}
		return outcome, nil
	}
	if scheme, ok := model.TypeChecker.Env().Get(resultBinding); ok && scheme != nil {
		outcome.Type = scheme.Type
	}
	env := object.NewEnvironment()
	if result := evaluator.Eval(model.Tree.Root, env); result != nil && result.Type() == object.ERROR_OBJ {
		return outcome, fmt.Errorf("%s", result.Inspect())
	}
	if value, ok := env.Get(resultBinding); ok {
		outcome.Value = value
	}
	return outcome, nil
}

// TypeOf checks an expression or type expression against the session.
func (s *Session) TypeOf(text string) (typechecker.Type, error) {
	model, err := s.compile(s.compose(nil, nil, text))
	if err != nil {
		return nil, err
	}
	if scheme, ok := model.TypeChecker.Env().Get(resultBinding); ok && scheme != nil {
		return scheme.Type, nil
	}
	return nil, fmt.Errorf("unknown type")
}

// Source is the session as a package file: imports first, then declarations.
func (s *Session) Source() string {
	return s.compose(nil, nil, "")
}

func (s *Session) compose(imports, declarations []string, expression string) string {
	var out strings.Builder
	all := append(append([]string(nil), s.imports...), imports...)
	for _, imp := range all {
		out.WriteString(imp)
		out.WriteString("\n")
	}
	for _, decl := range s.declarations {
		out.WriteString(decl)
		out.WriteString("\n\n")
	}
	for _, decl := range declarations {
		out.WriteString(decl)
		out.WriteString("\n\n")
	}
	if expression != "" {
		fmt.Fprintf(&out, "%s := %s\n", resultBinding, expression)
	}
	return out.String()
}

func parseInput(input string) (*ast.Program, error) {
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		return nil, fmt.Errorf("%s", strings.Join(errs, "\n"))
	}
	return program, nil
}

func declarationBinding(stmt ast.Statement) string {
	switch node := stmt.(type) {
	case *ast.FunctionStatement:
		if node.Name != nil {
			return node.Name.Value
		}
	case *ast.VariableDeclaration:
		if node.Name != nil {
			return node.Name.Value
		}
	}
	return ""
}

func (s *Session) compile(source string) (*compiler.SemanticModel, error) {
	return s.compileWith(source, false)
}

func (s *Session) compileWith(source string, strict bool) (*compiler.SemanticModel, error) {
	comp := compiler.New().
		WithSessionSources(s.ModuleDir, map[string]string{"repl.oak": source}).
		WithPlatformSizes(s.IntSize, s.PtrSize)
	if strict {
		comp = comp.WithProfile("strict")
	}
	return comp.SemanticModel().Get()
}

// Obligations lists what the checker could not discharge for the session
// program: the recorded assumptions and warnings every phase left standing
// (unsafe admissions, unbounded loops, unlowered tail cycles, runtime-
// initialized globals, ...). These are the inputs a proof-aware step would
// hand to Lean; the REPL surfaces them, it does not prove them.
func (s *Session) Obligations() ([]*diagnostic.Diagnostic, error) {
	if len(s.imports) == 0 && len(s.declarations) == 0 {
		return nil, nil
	}
	comp := compiler.New().
		WithSessionSources(s.ModuleDir, map[string]string{"repl.oak": s.Source()}).
		WithPlatformSizes(s.IntSize, s.PtrSize)
	model, err := comp.SemanticModel().Get()
	if err != nil {
		return nil, err
	}
	var open []*diagnostic.Diagnostic
	for _, d := range model.Diagnostics {
		if d != nil && d.Severity != diagnostic.SeverityError {
			open = append(open, d)
		}
	}
	sort.SliceStable(open, func(i, j int) bool {
		if open[i].Code != open[j].Code {
			return open[i].Code < open[j].Code
		}
		return open[i].Range.Start.Line < open[j].Range.Start.Line
	})
	return open, nil
}

// Law describes where a recorded obligation is modeled and what discharges
// it: the REPL's `:lean` hands the reader to the governing Lean module.
type Law struct {
	Module    string
	Statement string
	Discharge string
}

// laws maps recorded-assumption codes to their governing formal law.
var laws = map[string]Law{
	"OAK-D0103": {"Oak.BoundedLoop", "the canonical counter loop has a static iteration bound", "rewrite the loop in the canonical counter shape, or prove a ranking function for it"},
	"OAK-D0102": {"Oak.Discipline", "a rank certificate bounds stack depth and forces cycles to be tail-only", "make the cycle same-signature tail calls so the backend lowers it to a trampoline"},
	"OAK-B0110": {"Oak.Unsafe", "an unsafe assumption discharges exactly its own writable-disjointness obligation", "prove the regions disjoint statically, or keep the unsafe block and audit the recorded admission"},
	"OAK-B0109": {"Oak.Escape", "an escaping borrow of a scope-local owner dangles", "return an owned value; region-indexed signatures are the recorded headroom"},
	"OAK-T0501": {"Oak constitution (no hidden work)", "static storage is initialized before any code runs", "initialize at the top of main, or make the initializer a compile-time constant"},
	"OAK-T0202": {"Oak.PatternAnalysis", "a redundant arm is subsumed by earlier arms", "remove the arm"},
	"OAK-T0203": {"Oak.PatternAnalysis", "an impossible arm has no reachable case", "remove the arm"},
}

// LawFor returns the governing law of an obligation code, if modeled.
func LawFor(code string) (Law, bool) {
	law, ok := laws[code]
	return law, ok
}
