package compiler

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/stdlib"
)

// loadStandardLibrary resolves the bootstrap import explicitly. The initial
// module exports unqualified names; aliases and arbitrary packages fail closed.
// Parsing library source separately preserves its tokens and source identity.
func loadStandardLibrary(tree *SyntaxTree) error {
	var user []ast.Statement
	imported := false
	for _, stmt := range tree.Root.Statements {
		imp, ok := stmt.(*ast.ImportStatement)
		if !ok {
			user = append(user, stmt)
			continue
		}
		if imp.Path == nil || imp.Path.Value != "std" || imp.Alias != nil {
			return fmt.Errorf("import: only unaliased import(std) is supported by the bootstrap module loader")
		}
		imported = true
	}
	if !imported {
		return nil
	}
	lib, err := New().WithSource("std.oak", stdlib.Source).Parse().Get()
	if err != nil {
		return fmt.Errorf("standard library: %w", err)
	}
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
	exports := map[string]bool{"text_literal": true, "encode": true, "decode": true, "encoded_size": true, "from": true}
	for _, stmt := range lib.Root.Statements {
		if name := declarationName(stmt); name != "" {
			exports[name] = true
		}
	}
	for _, stmt := range user {
		if name := declarationName(stmt); exports[name] {
			return fmt.Errorf("import(std): declaration %q conflicts with a standard library export", name)
		}
	}
	tree.Root.Statements = append(lib.Root.Statements, user...)
	if err := lowerDerivedCodecs(tree.Root); err != nil {
		return err
	}
	if err := lowerTextLiterals(tree.Root); err != nil {
		return err
	}
	return lowerStdlibFluent(tree.Root)
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
