package compiler

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/borrowchecker"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/codegen/lean"
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
	// AsmUnits are the `.oakasm` translation units providing bodies for
	// definition-less declarations (docs/spec/94-assembler.md).
	AsmUnits []SourceText
	// LineDirectives makes the C backend emit #line directives so C
	// diagnostics and debuggers attribute generated code to Oak source
	// (docs/spec/90-backend.md section 10). Off by default: the generated C
	// then stands on its own lines for backend inspection.
	LineDirectives bool
}

// Compilation is the public, Roslyn-style compiler value. With* methods return
// modified copies so callers can cheaply derive configurations without hidden
// mutation between compiler phases.
type Compilation struct {
	source             SourceText
	options            Options
	resourceProtocols  []typechecker.ResourceProtocolDeclaration
	simulation         bool
	simulationBindings []SimulationBinding
	// Package build (compiler/modules.go): when packageDir is set, the
	// compilation loads the package directory and everything it imports
	// instead of the single source.
	packageDir   string
	includeTests bool
	moduleCache  string
	sessionFiles map[string]string
	// diagnosticSink observes every diagnostic a stage gate sees, rejecting
	// or not — how a driver surfaces informational findings such as the
	// assembler's verification verdicts (docs/spec/94-assembler.md §8).
	diagnosticSink func(*diagnostic.Diagnostic)
}

// WithDiagnosticSink returns a compilation that reports every diagnostic
// (including informational ones that never reject) to sink.
func (comp Compilation) WithDiagnosticSink(sink func(*diagnostic.Diagnostic)) Compilation {
	comp.diagnosticSink = sink
	return comp
}

// SyntaxTree is a parsed Oak source file.
type SyntaxTree struct {
	Source SourceText
	File   *source.File
	Root   *ast.Program
	// Modules carries the elaborator's facts for a package build; nil for a
	// single-source compilation.
	Modules *ModuleInfo
	// Prelude records which standard library prelude was spliced: "full"
	// (import(std)), "core" (library packages imported), or "".
	Prelude string
}

// SemanticModel owns type information for a syntax tree.
type SemanticModel struct {
	Tree *SyntaxTree
	// PublicRoot preserves the package's source declarations before stdlib
	// loading and generic/row specialization rewrite the executable tree.
	// Tooling that describes the package API must project from this surface,
	// never from compiler-generated declarations.
	PublicRoot  *ast.Program
	TypeChecker *typechecker.TypeChecker
	// Diagnostics are every diagnostic the phases recorded, warnings
	// included, whether or not the profile rejected them: the recorded
	// assumptions and undischarged checks a proof-aware tool can surface.
	Diagnostics []*diagnostic.Diagnostic
	// AsmFunctions are the checked asm-unit functions the backend emits as
	// top-level assembly blocks.
	AsmFunctions []*asm.Function
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

// WithAsmUnit adds one `.oakasm` translation unit (docs/spec/94-assembler.md):
// its functions provide the bodies of the source's definition-less
// declarations with identical signatures.
func (comp Compilation) WithAsmUnit(path, text string) Compilation {
	comp.options.AsmUnits = append(append([]SourceText(nil), comp.options.AsmUnits...), SourceText{Path: path, Text: text})
	return comp
}

// WithLineDirectives returns a compilation whose generated C carries #line
// directives mapping functions and statements to their Oak source lines.
func (comp Compilation) WithLineDirectives() Compilation {
	comp.options.LineDirectives = true
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

// WithResourceProtocols configures syntax-independent resource semantics for
// the ordinary Check pipeline. These declarations are resolved against Oak's
// checked type/callable environment; this API intentionally freezes no source
// spelling for resource protocols, consumption, or fresh authority.
func (comp Compilation) WithResourceProtocols(declarations []typechecker.ResourceProtocolDeclaration) Compilation {
	comp.resourceProtocols = cloneResourceProtocolDeclarations(declarations)
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
	if comp.packageDir != "" {
		return Value(comp.packageDir).Then(func(string) (*SyntaxTree, error) {
			return comp.parsePackageBuild()
		})
	}
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
// checking (memory safety), configured resource-authority checking, and
// discipline analysis (bounded execution) all gate compilation. Resource
// semantics enter through syntax-independent resolved declarations rather than
// a source spelling. Error-severity diagnostics always reject; in the strict
// profile, warnings (recorded unsafe assumptions, tail-recursion obligations,
// unnecessary-code warnings) reject too (85-discipline §7).
func (comp Compilation) Check() Stage[*SemanticModel] {
	return comp.check(comp.resourceProtocols)
}

func (comp Compilation) check(resourceProtocols []typechecker.ResourceProtocolDeclaration) Stage[*SemanticModel] {
	return comp.Parse().Then(func(tree *SyntaxTree) (*SemanticModel, error) {
		publicSource := tree.Root
		if tree.Modules != nil && tree.Modules.Public != nil {
			publicSource = tree.Modules.Public
		}
		publicRoot, ok := cloneSyntax(reflect.ValueOf(publicSource)).Interface().(*ast.Program)
		if !ok || publicRoot == nil {
			return nil, fmt.Errorf("compiler: cannot preserve public syntax surface")
		}
		if err := loadStandardLibrary(tree); err != nil {
			return nil, err
		}
		// Protocol declarations (compiler/protocols.go) project into the
		// types and functions the rest of the pipeline sees, and into the
		// resource facts checked after typing.
		protocolFacts, err := lowerProtocols(tree)
		if err != nil {
			return nil, err
		}
		if len(protocolFacts) != 0 {
			resourceProtocols = append(cloneResourceProtocolDeclarations(resourceProtocols), protocolFacts...)
		}
		// Type-qualified variant construction (compiler/variants.go) and
		// derived declarations (compiler/derive.go) are resolved once the
		// whole program, imports included, is in one tree.
		if err := lowerDerived(tree, comp); err != nil {
			return nil, err
		}
		if err := lowerLibrarySugar(tree); err != nil {
			return nil, err
		}
		if err := lowerQualifiedVariants(tree.Root); err != nil {
			return nil, err
		}
		if comp.simulation {
			if err := checkSimulation(tree.Root, comp.simulationBindings); err != nil {
				return nil, err
			}
		}
		// Asm units pair with definition-less declarations and pass the
		// assembler's seam checker before type checking sees the program
		// (docs/spec/94-assembler.md).
		asmFunctions, asmDiagnostics := comp.stitchAsmUnits(tree.Root)
		if err := comp.gate("asm", asmDiagnostics, tree.Modules); err != nil {
			return nil, err
		}
		env := object.NewEnvironment()
		tc := typechecker.NewWithPlatformSizes(env, comp.options.IntSize, comp.options.PtrSize)
		if tree.Modules != nil {
			tc.SetModuleContext(tree.Modules.OpaqueTypes, tree.Modules.Packages)
			tc.SetPackageExports(tree.Modules.Exports)
			tc.SetSealedOpaque(tree.Modules.SealedOpaque)
			tc.SetAbstractTypes(tree.Modules.Abstract)
		}
		// The spliced bootstrap library is stamped `std` (compiler/stdlib.go)
		// and is a package of its own for scoping purposes.
		tc.AddPackagePaths("std")
		tc.CheckProgram(tree.Root)
		if tree.Modules != nil {
			// Sealed-import member types (docs/spec/83-modules.md section 6.3).
			tc.CheckSignatureObligations(tree.Modules.Obligations)
			tc.CheckParameterObligations(tree.Modules.Parameters)
		}
		if err := comp.gate("typecheck", tc.Diagnostics(), tree.Modules); err != nil {
			return nil, err
		}

		model := &SemanticModel{Tree: tree, PublicRoot: publicRoot, TypeChecker: tc, AsmFunctions: asmFunctions}
		model.Diagnostics = append(model.Diagnostics, tc.Diagnostics()...)

		bc := borrowchecker.New()
		bc.CheckProgram(tree.Root, tc.Env())
		model.Diagnostics = append(model.Diagnostics, bc.Diagnostics()...)
		if err := comp.gate("borrowcheck", bc.Diagnostics(), tree.Modules); err != nil {
			return nil, err
		}

		if len(resourceProtocols) != 0 {
			if _, _, err := comp.checkResourceProtocols(model, resourceProtocols); err != nil {
				return nil, err
			}
		}

		disciplineDiagnostics := discipline.AnalyzeProgram(tree.Root).Diagnostics()
		model.Diagnostics = append(model.Diagnostics, disciplineDiagnostics...)
		if err := comp.gate("discipline", disciplineDiagnostics, tree.Modules); err != nil {
			return nil, err
		}
		// Effect clauses (compiler/effects.go): forbids is checked over the
		// specialized call graph, so every callee here is concrete.
		steady := map[string]string{}
		if tree.Modules != nil {
			steady = applySteadyEntries(tree.Root, tree.Modules.Steady)
		}
		effectDiagnostics := analyzeEffects(tree.Root, steady)
		model.Diagnostics = append(model.Diagnostics, effectDiagnostics...)
		if err := comp.gate("effects", effectDiagnostics, tree.Modules); err != nil {
			return nil, err
		}

		return model, nil
	})
}

// gate rejects on error diagnostics, and on warnings too where the strict
// profile applies (zero-warning rule). Profiles are per module
// (docs/spec/85-discipline.md section 1): a warning rejects when the
// effective profile of the package owning its primary cause is strict.
func (comp Compilation) gate(phase string, diagnostics []*diagnostic.Diagnostic, info *ModuleInfo) error {
	if comp.diagnosticSink != nil {
		for _, d := range diagnostics {
			if d != nil {
				comp.diagnosticSink(d)
			}
		}
	}
	rejecting := diagnosticErrors(diagnostics)
	for _, d := range diagnostics {
		if d.Severity == diagnostic.SeverityWarning && comp.profileFor(d.Package, info) == "strict" {
			rejecting = append(rejecting, d)
		}
	}
	if len(rejecting) != 0 {
		return &DiagnosticError{Phase: phase, Diagnostics: rejecting}
	}
	return nil
}

// profileFor resolves the discipline profile a package is judged under.
//
//   - Root-module packages, the root of a single-source build, and any
//     diagnostic whose package is unknown take the root profile: the
//     command-line/Options profile when given, else the root manifest's
//     declaration, else "default". Unknown is treated as root deliberately —
//     monomorphized clones of generic functions carry their instantiation
//     name rather than a package — so a strict root never loses a warning to
//     a missing stamp.
//   - Packages of a dependency module take that module's declared profile,
//     "default" when it declares none.
//   - The spliced bootstrap library (`std`, `testing-host`) and standard
//     library packages, which have no manifest, are judged under "default".
func (comp Compilation) profileFor(pkg string, info *ModuleInfo) string {
	rootProfile := comp.options.Profile
	if rootProfile == "" && info != nil {
		rootProfile = info.ModuleProfiles[info.RootModule]
	}
	if rootProfile == "" {
		rootProfile = "default"
	}
	switch pkg {
	case "":
		return rootProfile
	case "std", "testing-host":
		return "default"
	}
	if info == nil || pkg == info.RootPackage {
		return rootProfile
	}
	if info.StandardLibrary[pkg] {
		return "default" // no module, no manifest
	}
	if module, owned := info.ModuleOf[pkg]; owned && module != info.RootModule {
		if declared := info.ModuleProfiles[module]; declared != "" {
			return declared
		}
		return "default"
	}
	return rootProfile
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
		generator.SetAsmFunctions(lowered.Model.AsmFunctions)
		generator.SetSourceFile(lowered.Model.Tree.Source.Path)
		generator.SetLineDirectives(comp.options.LineDirectives)
		if lowered.Model.Tree.Modules != nil {
			generator.SetAbstractAliases(lowered.Model.Tree.Modules.Abstract)
		}
		generator.SetSourceText(lowered.Model.Tree.Source.Text)
		return generator.Generate(lowered.Root, lowered.Model.TypeChecker)
	})
}

// EmitHeader emits the C header of the program's exported surface: the
// generated C's typedefs, every declared type with its layout assertions,
// and a prototype per `pub` function (docs/spec/92-ffi.md section 2.6).
func (comp Compilation) EmitHeader() Stage[string] {
	return comp.Lower().Then(func(lowered *LoweredProgram) (string, error) {
		generator := codegen.New(comp.options.PackageName, lowered.Model.TypeChecker)
		generator.SetSourceFile(lowered.Model.Tree.Source.Path)
		if lowered.Model.Tree.Modules != nil {
			generator.SetAbstractAliases(lowered.Model.Tree.Modules.Abstract)
		}
		return generator.GenerateHeader(lowered.Root, lowered.Model.TypeChecker)
	})
}

// EmitLean extracts the program's own declarations (never the spliced
// standard library) into Lean 4 definitions under the given namespace
// (docs/spec/95-extraction.md, codegen/lean). The extraction reads the
// type-checked tree before lowering, so it sees the program as written.
func (comp Compilation) EmitLean(namespace string) Stage[string] {
	return comp.Check().Then(func(model *SemanticModel) (string, error) {
		names := map[string]bool{}
		if model.PublicRoot != nil {
			for _, stmt := range model.PublicRoot.Statements {
				switch s := stmt.(type) {
				case *ast.FunctionStatement:
					if s.Name != nil {
						names[s.Name.Value] = true
					}
				case *ast.ADTType:
					if s.Name != nil {
						names[s.Name.Value] = true
					}
				}
			}
		} else {
			names = nil
		}
		return lean.Emit(model.Tree.Root, model.TypeChecker, namespace, names)
	})
}

func phaseError(phase string, errors []string) error {
	return fmt.Errorf("%s failed: %s", phase, strings.Join(errors, "; "))
}
