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
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
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
	comp := compiler.New().
		WithSessionSources(s.ModuleDir, map[string]string{"repl.oak": source}).
		WithPlatformSizes(s.IntSize, s.PtrSize)
	model, err := comp.SemanticModel().Get()
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
	source := s.compose(nil, nil, text)
	comp := compiler.New().
		WithSessionSources(s.ModuleDir, map[string]string{"repl.oak": source}).
		WithPlatformSizes(s.IntSize, s.PtrSize)
	model, err := comp.SemanticModel().Get()
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
