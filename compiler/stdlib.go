package compiler

import (
	"fmt"
	"reflect"
	"sync"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/stdlib"
)

// loadStandardLibrary resolves the bootstrap import explicitly. The initial
// module exports unqualified names; aliases and arbitrary packages fail closed.
// Parsing library source separately preserves its tokens and source identity.
func loadStandardLibrary(tree *SyntaxTree) error {
	var user []ast.Statement
	imported := false
	testingImported := false
	for _, stmt := range tree.Root.Statements {
		imp, ok := stmt.(*ast.ImportStatement)
		if !ok {
			user = append(user, stmt)
			continue
		}
		if imp.Path == nil || imp.Alias != nil {
			return fmt.Errorf("import: only unaliased import(std) and import(testing) are supported")
		}
		switch imp.Path.Value {
		case "std":
			imported = true
		case "testing":
			testingImported = true
		default:
			return fmt.Errorf("import: unsupported module %q", imp.Path.Value)
		}
	}
	coreOnly := !imported && tree.Modules != nil && tree.Modules.PreludeCore
	if !imported && !testingImported && !coreOnly {
		return nil
	}
	librarySource := ""
	if imported {
		librarySource = stdlib.Source
	} else if coreOnly {
		// Standard library packages build on the core prelude (std.oak)
		// unqualified (docs/spec/83-modules.md section 9).
		librarySource = stdlib.Prelude
	}
	if testingImported {
		librarySource += "\n" + stdlib.TestingSource
	}
	lib, err := New().WithSource("stdlib.oak", librarySource).Parse().Get()
	if err != nil {
		return fmt.Errorf("standard library: %w", err)
	}
	// The spliced library is its own package for scoping and diagnostics
	// (docs/spec/83-modules.md section 7): every token is stamped
	// `std#stdlib.oak`, so a local in the prelude is checked against the
	// prelude's scope rather than the root's, and a discipline diagnostic
	// inside the prelude names its file and line.
	stampSemanticContext(reflect.ValueOf(lib.Root), "std#stdlib.oak")
	if err := transformSyntax(reflect.ValueOf(lib.Root), func(e ast.Expression) (ast.Expression, error) {
		switch n := e.(type) {
		case *ast.InfixExpression:
			n.Token.SemanticContext = "std"
		case *ast.MatchExpression:
			n.Token.SemanticContext = "std"
		case *ast.VariantExpression:
			n.Token.SemanticContext = "std"
		}
		return e, nil
	}); err != nil {
		return err
	}
	exports := map[string]bool{}
	if imported {
		for _, name := range []string{"text_literal", "encode", "decode", "encoded_size", "from"} {
			exports[name] = true
		}
	}
	for _, stmt := range lib.Root.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.ExternSymbol != "" && testingImported {
			fn.Token.SemanticContext = "testing-host"
		}
		if name := declarationName(stmt); name != "" {
			exports[name] = true
		}
	}
	for _, stmt := range user {
		if name := declarationName(stmt); exports[name] {
			return fmt.Errorf("import: declaration %q conflicts with a standard library export", name)
		}
	}
	tree.Root.Statements = append(lib.Root.Statements, user...)
	if imported {
		tree.Prelude = "full"
	} else if coreOnly {
		tree.Prelude = "core"
	}
	return nil
}

// lowerLibrarySugar runs the standard library's static sugar — derived JSON
// codecs, typed text literals, fluent builder calls — over the whole program.
// The sugar generates calls to library functions by their flat names; in a
// program that imports library packages by path (docs/spec/83-modules.md
// section 9) those names are resolved to the packages' internal names, and a
// name whose package is not imported fails closed with a diagnostic naming
// the import to add. It runs after module elaboration and derivation, so
// derived bodies may use the same sugar.
func lowerLibrarySugar(tree *SyntaxTree) error {
	names := libraryNames{}
	if tree.Modules != nil {
		names.internal = tree.Modules.LibraryNames
	}
	if tree.Prelude != "full" && len(names.internal) == 0 {
		// No library in scope: the sugar's entry points are ordinary
		// undefined names for the checker to report.
		return nil
	}
	if err := lowerDerivedCodecs(tree.Root); err != nil {
		return err
	}
	if err := lowerTextLiterals(tree.Root); err != nil {
		return err
	}
	if err := lowerStdlibFluent(tree.Root, names); err != nil {
		return err
	}
	if len(names.internal) == 0 {
		return nil
	}
	return names.apply(tree.Root)
}

// libraryNames resolves flat library names in generated sugar to the loaded
// packages' internal names. An empty map is the flat prelude: identity.
type libraryNames struct {
	internal map[string]string
}

// resolve maps a flat library name. It fails when the name belongs to a
// standard library package the program did not import.
func (n libraryNames) resolve(flat string) (string, error) {
	if len(n.internal) == 0 {
		return flat, nil
	}
	if internal, loaded := n.internal[flat]; loaded {
		return internal, nil
	}
	if owner, isLibrary := stdlibOwner(flat); isLibrary {
		return "", fmt.Errorf("%s belongs to the standard library package %q; add import(%q)", flat, owner, owner)
	}
	return flat, nil
}

// apply renames flat library names throughout the program (generated sugar
// and derived bodies use flat spellings). Root declarations shadow nothing:
// a name the root package declares itself is never rewritten.
func (n libraryNames) apply(program *ast.Program) error {
	rootDeclared := map[string]bool{}
	for _, stmt := range program.Statements {
		if name := declarationName(stmt); name != "" && !modules.Reserved(name) {
			rootDeclared[name] = true
		}
	}
	var failure error
	(&syntaxVisitor{ident: func(id *ast.Identifier, label bool) {
		if label || rootDeclared[id.Value] || failure != nil {
			return
		}
		if internal, loaded := n.internal[id.Value]; loaded {
			id.Value = internal
			return
		}
		if owner, isLibrary := stdlibOwner(id.Value); isLibrary {
			failure = fmt.Errorf("%s belongs to the standard library package %q; add import(%q)", id.Value, owner, owner)
		}
	}}).walk(reflect.ValueOf(program), false)
	return failure
}

var (
	stdlibOwnersOnce sync.Once
	stdlibOwners     map[string]string
)

// stdlibOwner reports which standard library package declares a flat name.
// The core prelude's names are not owned by any package.
func stdlibOwner(flat string) (string, bool) {
	stdlibOwnersOnce.Do(func() {
		stdlibOwners = map[string]string{}
		for path, text := range stdlib.Packages {
			tree, err := New().WithSource(path+".oak", text).Parse().Get()
			if err != nil {
				continue
			}
			for _, stmt := range tree.Root.Statements {
				if name := declarationName(stmt); name != "" {
					stdlibOwners[name] = path
				}
			}
		}
	})
	owner, ok := stdlibOwners[flat]
	return owner, ok
}

func declarationName(stmt ast.Statement) string {
	switch s := stmt.(type) {
	case *ast.ADTType:
		return s.Name.Value
	case *ast.FunctionStatement:
		return s.Name.Value
	case *ast.VariableDeclaration:
		return s.Name.Value
	case *ast.InterfaceType:
		return s.Name.Value
	}
	return ""
}
