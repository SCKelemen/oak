// Package testrunner implements the host side of oak test. Test bodies always
// pass through Compilation.EmitC and execute as native, isolated processes.
package testrunner

import (
 "fmt"
 "io/fs"
 "os"
 "path/filepath"
 "regexp"
 "sort"
 "strings"

 "github.com/SCKelemen/oak/ast"
 "github.com/SCKelemen/oak/compiler"
)

type Test struct {
 Name string `json:"name"`
 File string `json:"file"`
 Line int `json:"line"`
 Kind string `json:"kind"`
}

type Package struct {
 Dir string
 Source string
 Tests []Test
 Registry []Test
}

var cIdentifier = regexp.MustCompile(`^[A-Za-z_][A-Za-z_0-9]*$`)

// Discover treats each directory as a bootstrap package. Only *_test.oak files
// register tests; all sibling .oak files supply production code and helpers.
// Recursive discovery excludes hidden directories, vendor and testdata.
func Discover(paths []string) ([]Package, error) {
 if len(paths) == 0 { paths = []string{"."} }
 dirs := map[string]bool{}
 for _, path := range paths {
  recursive := path == "..." || strings.HasSuffix(path, string(filepath.Separator)+"...")
  if recursive {
   root := strings.TrimSuffix(path, "...")
   if root == "" { root = "." }
   err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
    if err != nil { return err }
    if d.IsDir() {
     if p != root && (strings.HasPrefix(d.Name(), ".") || d.Name() == "vendor" || d.Name() == "testdata") { return filepath.SkipDir }
    } else if strings.HasSuffix(d.Name(), "_test.oak") { dirs[filepath.Dir(p)] = true }
    return nil
   })
   if err != nil { return nil, err }
  } else {
   info, err := os.Stat(path)
   if err != nil { return nil, err }
   if !info.IsDir() { return nil, fmt.Errorf("oak test expects a directory or ./..., got %s", path) }
   dirs[path] = true
  }
 }
 canonical := map[string]bool{}
 for dir := range dirs { abs, err := filepath.Abs(dir); if err != nil { return nil, err }; canonical[abs] = true }
 names := make([]string, 0, len(canonical))
 for dir := range canonical { names = append(names, dir) }
 sort.Strings(names)
 var packages []Package
 for _, dir := range names {
  entries, err := os.ReadDir(dir)
  if err != nil { return nil, err }
  var pkg Package
  pkg.Dir = dir
  var src strings.Builder
  for _, entry := range entries {
   if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") || strings.HasPrefix(entry.Name(), ".") { continue }
   path := filepath.Join(dir, entry.Name())
   data, err := os.ReadFile(path)
   if err != nil { return nil, err }
   // Newlines prevent final comments/layout blocks from eating the next file.
   fmt.Fprintf(&src, "\n// oak test source: %s\n%s\n", entry.Name(), data)
   if !strings.HasSuffix(entry.Name(), "_test.oak") { continue }
   tree, err := compiler.New().WithSource(path, string(data)).Parse().Get()
   if err != nil { return nil, fmt.Errorf("%s: %w", path, err) }
   for _, stmt := range tree.Root.Statements {
    fn, ok := stmt.(*ast.FunctionStatement)
    if !ok || fn.Name == nil { continue }
    kind := testKind(fn.Name.Value)
    if kind == "" { continue }
    if err := validateTest(fn, kind); err != nil { return nil, fmt.Errorf("%s:%d: %w", path, fn.Token.Line, err) }
    pkg.Tests = append(pkg.Tests, Test{Name: fn.Name.Value, File: entry.Name(), Line: fn.Token.Line, Kind: kind})
   }
  }
  pkg.Source = src.String()
  sort.Slice(pkg.Tests, func(i,j int) bool { return pkg.Tests[i].Name < pkg.Tests[j].Name })
  for i := 1; i < len(pkg.Tests); i++ { if pkg.Tests[i-1].Name == pkg.Tests[i].Name { return nil, fmt.Errorf("duplicate test %s in %s", pkg.Tests[i].Name, dir) } }
  pkg.Registry = append([]Test(nil), pkg.Tests...)
  if len(pkg.Tests) != 0 { packages = append(packages, pkg) }
 }
 return packages, nil
}

func testKind(name string) string {
 for _, p := range []struct{prefix, kind string}{{"Property", "property"}, {"Fuzz", "fuzz"}, {"Sim", "simulation"}, {"Test", "unit"}} {
  if strings.HasPrefix(name, p.prefix) && len(name) > len(p.prefix) {
   next := name[len(p.prefix)]
   if next == '_' || next >= 'A' && next <= 'Z' { return p.kind }
  }
 }
 return ""
}

func validateTest(fn *ast.FunctionStatement, kind string) error {
 bad := func() error { return fmt.Errorf("%s must be a non-generic %s test returning (), with %s", fn.Name.Value, kind, map[bool]string{true:"no arguments", false:"one []u8 argument"}[kind == "unit"]) }
 if !cIdentifier.MatchString(fn.Name.Value) || fn.Receiver != nil || len(fn.TypeParams) != 0 || fn.ExternSymbol != "" { return bad() }
 ret, ok := fn.ReturnType.(*ast.Identifier)
 if !ok || ret.Value != "()" { return bad() }
 if kind == "unit" { if len(fn.Parameters) != 0 { return bad() }; return nil }
 if len(fn.Parameters) != 1 || fn.Parameters[0].Variadic { return bad() }
 view, ok := fn.Parameters[0].Type.(*ast.IndexExpression)
 if !ok || view.Dot { return bad() }
 element, eok := view.Left.(*ast.Identifier)
 marker, mok := view.Index.(*ast.Identifier)
 if !eok || !mok || element.Value != "u8" || marker.Value != "" { return bad() }
 return nil
}
