package compiler

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/lowering"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// SourceText is the source identity carried through the compiler pipeline.
type SourceText struct {
	Path string
	Text string
}

// Options contains target-independent compilation options. More target and
// semantic options can be added without widening every compiler phase API.
type Options struct {
	PackageName string
	IntSize     int
	PtrSize     int
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
	Root   *ast.Program
}

// SemanticModel owns type information for a syntax tree.
type SemanticModel struct {
	Tree        *SyntaxTree
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

// Options returns the effective compilation options.
func (comp Compilation) Options() Options {
	return comp.options
}

// Source returns the effective source.
func (comp Compilation) Source() SourceText {
	return comp.source
}

// Parse produces the syntax tree. This method is intentionally the only place
// in the facade that constructs the parser; layout normalization will be wired
// here once Parser accepts the shared token-source interface.
func (comp Compilation) Parse() Stage[*SyntaxTree] {
	return Value(comp.source).Then(func(source SourceText) (*SyntaxTree, error) {
		p := parser.New(scanner.New(source.Text))
		root := p.ParseProgram()
		if errors := p.Errors(); len(errors) != 0 {
			return nil, phaseError("parse", errors)
		}
		return &SyntaxTree{Source: source, Root: root}, nil
	})
}

// SyntaxTree is the Roslyn-style spelling for Parse.
func (comp Compilation) SyntaxTree() Stage[*SyntaxTree] {
	return comp.Parse()
}

// Check parses and type-checks the source.
func (comp Compilation) Check() Stage[*SemanticModel] {
	return comp.Parse().Then(func(tree *SyntaxTree) (*SemanticModel, error) {
		env := object.NewEnvironment()
		tc := typechecker.NewWithPlatformSizes(env, comp.options.IntSize, comp.options.PtrSize)
		tc.CheckProgram(tree.Root)
		if errors := tc.Errors(); len(errors) != 0 {
			return nil, phaseError("typecheck", errors)
		}
		return &SemanticModel{Tree: tree, TypeChecker: tc}, nil
	})
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
		generator := codegen.New(comp.options.PackageName, lowered.Model.TypeChecker)
		generator.SetSourceFile(lowered.Model.Tree.Source.Path)
		generator.SetSourceText(lowered.Model.Tree.Source.Text)
		return generator.Generate(lowered.Root, lowered.Model.TypeChecker)
	})
}

func phaseError(phase string, errors []string) error {
	return fmt.Errorf("%s failed: %s", phase, strings.Join(errors, "; "))
}
