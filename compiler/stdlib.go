package compiler

import (
 "fmt"
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
  if !ok { user = append(user, stmt); continue }
  if imp.Path == nil || imp.Path.Value != "std" || imp.Alias != nil {
   return fmt.Errorf("import: only unaliased import(std) is supported by the bootstrap module loader")
  }
  imported = true
 }
 if !imported { return nil }
 lib, err := New().WithSource("std.oak", stdlib.Source).Parse().Get()
 if err != nil { return fmt.Errorf("standard library: %w", err) }
 exports := map[string]bool{}
 for _, stmt := range lib.Root.Statements {
  if name := declarationName(stmt); name != "" { exports[name] = true }
 }
 for _, stmt := range user {
  if name := declarationName(stmt); exports[name] {
   return fmt.Errorf("import(std): declaration %q conflicts with a standard library export", name)
  }
 }
 tree.Root.Statements = append(lib.Root.Statements, user...)
 return nil
}

func declarationName(stmt ast.Statement) string {
 switch s := stmt.(type) {
 case *ast.ADTType: return s.Name.Value
 case *ast.FunctionStatement: return s.Name.Value
 case *ast.VariableDeclaration: return s.Name.Value
 case *ast.InterfaceType: return s.Name.Value
 }
 return ""
}
