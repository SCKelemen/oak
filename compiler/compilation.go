package compiler

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/borrowchecker"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/lowering"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/typechecker"
)

// SourceText is the source identity carried through the compiler pipeline.
type SourceText struct {
	Path string
	Text string
}

func (s SourceText) File(id source.ID) *source.File {
	return source.NewFile(id, s.Path, s.Text)
}

// Options contains target-independent compilation options. More target and
// semantic options can be added without widening every compiler phase API.
type Options struct {
	PackageName string
	IntSize     int
	PtrSize     int
	// Profile selects the discipline profile (docs/spec/85-discipline.md):
	// "default" gates on error-severity diagnostics only; "strict" promotes
	// every warning (recorded unsafe assumptions, tail-recursion
	// obligations, unnecessary-code warnings) to a rejection.
	Profile string
}

// Compilation is the public, Roslyn-style compiler value. With* methods return
// modified copies so callers can cheaply derive configurations without hidden
// mutation between compiler phases.
type Compilation struct {
	source  SourceText
	options Options
}

// SyntaxTree is a parsed Oak source file.
type SyntaxTree struct {
	Source SourceText
	File   *source.File
	Root   *ast.Program
}

// SemanticModel owns type information for a syntax tree.
type SemanticModel struct {
	Tree        *SyntaxTree
	// PublicRoot preserves the package's source declarations before stdlib
	// loading and generic/row specialization rewrite the executable tree.
	// Tooling that describes the package API must project from this surface,
	// never from compiler-generated declarations.
	PublicRoot  *ast.Program
	TypeChecker *typechecker.TypeChecker
}

// LoweredProgram is the executable-oriented AST plus its semantic model.
type LoweredProgram struct {
	Model *SemanticModel
	Root  *ast.Program
}

// New returns a compilation with deterministic 64-bit defaults.
func New() Compilation {
	return Compilation{
		source: SourceText{
			Path: "main.oak",
		},
		options: Options{
			PackageName: "main",
			IntSize:     64,
			PtrSize:     64,
		},
	}
}

// WithSource returns a compilation using path/text as its source.
func (comp Compilation) WithSource(path, text string) Compilation {
	comp.source = SourceText{Path: path, Text: text}
	return comp
}

// WithPackageName returns a compilation configured for packageName.
func (comp Compilation) WithPackageName(packageName string) Compilation {
	comp.options.PackageName = packageName
	return comp
}

// WithPlatformSizes returns a compilation configured for machine-sized integer
// and pointer widths. The type checker remains the authority for validating
// supported widths.
func (comp Compilation) WithPlatformSizes(intSize, ptrSize int) Compilation {
	comp.options.IntSize = intSize
	comp.options.PtrSize = ptrSize
	return comp
}

// WithProfile returns a compilation using the given discipline profile
// ("default" or "strict", docs/spec/85-discipline.md section 1).
func (comp Compilation) WithProfile(profile string) Compilation {
	comp.options.Profile = profile
	return comp
}

// Options returns the effective compilation options.
func (comp Compilation) Options() Options {
	return comp.options
}

// Source returns the effective source.
func (comp Compilation) Source() SourceText {
	return comp.source
}

// Parse produces the syntax tree through the canonical front-end pipeline.
// Explicit braces pass through layout unchanged; indentation-delimited bodies
// become synthetic braces before the parser sees them. Both surface styles
// therefore share one parser and one AST semantics.
func (comp Compilation) Parse() Stage[*SyntaxTree] {
	return Value(comp.source).Then(func(text SourceText) (*SyntaxTree, error) {
		// Source-decoder validation (docs/spec/70-strings.md section 8,
		// Oak.Utf8Validity): string literals inherit their validity from the
		// whole file being valid UTF-8, so invalid bytes are rejected at
		// ingestion instead of flowing byte-exact into `string` values and
		// generated C.
		if offset, ok := source.ValidateUTF8(text.Text); !ok {
			return nil, phaseError("source", []string{
				fmt.Sprintf("source is not valid UTF-8 at byte offset %d", offset),
			})
		}
		file := text.File(1)
		tokens := layout.New(scanner.NewFile(file))
		p := parser.New(tokens)
		root := p.ParseProgram()
		if errors := p.Errors(); len(errors) != 0 {
			return nil, phaseError("parse", errors)
		}
		return &SyntaxTree{Source: text, File: file, Root: root}, nil
	})
}

// SyntaxTree is the Roslyn-style spelling for Parse.
func (comp Compilation) SyntaxTree() Stage[*SyntaxTree] {
	return comp.Parse()
}

// Check parses and semantically checks the source: type checking, borrow
// checking (memory safety), and discipline analysis (bounded execution) all
// gate compilation. Error-severity diagnostics always reject; in the strict
// profile, warnings (recorded unsafe assumptions, tail-recursion
// obligations, unnecessary-code warnings) reject too (85-discipline §7).
func (comp Compilation) Check() Stage[*SemanticModel] {
	return comp.Parse().Then(func(tree *SyntaxTree) (*SemanticModel, error) {
		publicRoot, ok := cloneSyntax(reflect.ValueOf(tree.Root)).Interface().(*ast.Program)
		if !ok || publicRoot == nil {
			return nil, fmt.Errorf("compiler: cannot preserve public syntax surface")
		}
		if err := loadStandardLibrary(tree); err != nil {
			return nil, err
		}
		env := object.NewEnvironment()
		tc := typechecker.NewWithPlatformSizes(env, comp.options.IntSize, comp.options.PtrSize)
		tc.CheckProgram(tree.Root)
		if err := comp.gate("typecheck", tc.Diagnostics()); err != nil {
			return nil, err
		}

		bc := borrowchecker.New()
		bc.CheckProgram(tree.Root, tc.Env())
		if err := comp.gate("borrowcheck", bc.Diagnostics()); err != nil {
			return nil, err
		}

		if err := comp.gate("discipline", discipline.AnalyzeProgram(tree.Root).Diagnostics()); err != nil {
			return nil, err
		}

		return &SemanticModel{Tree: tree, PublicRoot: publicRoot, TypeChecker: tc}, nil
	})
}

// gate rejects on error diagnostics, and on warnings too in the strict
// profile (zero-warning rule).
func (comp Compilation) gate(phase string, diagnostics []*diagnostic.Diagnostic) error {
	rejecting := diagnosticErrors(diagnostics)
	if comp.options.Profile == "strict" {
		for _, d := range diagnostics {
			if d.Severity == diagnostic.SeverityWarning {
				rejecting = append(rejecting, d)
			}
		}
	}
	if len(rejecting) != 0 {
		return &DiagnosticError{Phase: phase, Diagnostics: rejecting}
	}
	return nil
}

// SemanticModel is the Roslyn-style spelling for Check.
func (comp Compilation) SemanticModel() Stage[*SemanticModel] {
	return comp.Check()
}

// Lower parses, checks, and lowers high-level operations to the core AST.
func (comp Compilation) Lower() Stage[*LoweredProgram] {
	return comp.Check().Map(func(model *SemanticModel) *LoweredProgram {
		return &LoweredProgram{
			Model: model,
			Root:  lowering.LowerProgram(model.Tree.Root, model.TypeChecker),
		}
	})
}

// EmitC runs the current C backend through the same fluent compilation value.
func (comp Compilation) EmitC() Stage[string] {
	return comp.Lower().Then(func(lowered *LoweredProgram) (string, error) {
		for _, stmt := range lowered.Root.Statements {
			if fn, ok := stmt.(*ast.FunctionStatement); ok && len(fn.TypeParams) != 0 {
				return "", fmt.Errorf("codegen: generic function %s requires supported explicit specialization", fn.Name.Value)
			}
		}
		generator := codegen.New(comp.options.PackageName, lowered.Model.TypeChecker)
		generator.SetSourceFile(lowered.Model.Tree.Source.Path)
		generator.SetSourceText(lowered.Model.Tree.Source.Text)
		return generator.Generate(lowered.Root, lowered.Model.TypeChecker)
	})
}

func phaseError(phase string, errors []string) error {
	return fmt.Errorf("%s failed: %s", phase, strings.Join(errors, "; "))
}
