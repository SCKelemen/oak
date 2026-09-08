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
	Generator string `json:"generator,omitempty"`
	Name      string `json:"name"`
	File      string `json:"file"`
	Line      int    `json:"line"`
	Kind      string `json:"kind"`
}

type Package struct {
	Dir string
	// Name is the package clause of a module package (docs/spec/83-modules.md);
	// empty for a bootstrap package assembled by concatenation.
	Name     string
	Module   bool
	Source   string
	Tests    []Test
	Registry []Test
}

// symbol is the C name the generated translation unit gives a top-level
// function of the root package: root declarations keep their source names
// whatever the package clause says (docs/spec/83-modules.md section 7,
// compiler/modules.go merge); only imported packages are renamed.
func (p Package) symbol(name string) string {
	return "oak_" + name
}

// packageClause returns the package name declared by the first statement of
// an Oak source file, or "" when the file has no package clause.
func packageClause(source string) string {
	for _, line := range strings.Split(source, "\n") {
		trimmed := strings.TrimSpace(line)
		if trimmed == "" || strings.HasPrefix(trimmed, "//") {
			continue
		}
		if name, ok := strings.CutPrefix(trimmed, "package "); ok {
			return strings.TrimSpace(name)
		}
		return ""
	}
	return ""
}

var cIdentifier = regexp.MustCompile(`^[A-Za-z_][A-Za-z_0-9]*$`)

// Discover treats each directory as a bootstrap package. Only *_test.oak files
// register tests; all sibling .oak files supply production code and helpers.
// Recursive discovery excludes hidden directories, vendor and testdata.
func Discover(paths []string) ([]Package, error) {
	if len(paths) == 0 {
		paths = []string{"."}
	}
	dirs := map[string]bool{}
	for _, path := range paths {
		recursive := path == "..." || strings.HasSuffix(path, string(filepath.Separator)+"...")
		if recursive {
			root := strings.TrimSuffix(path, "...")
			if root == "" {
				root = "."
			}
			err := filepath.WalkDir(root, func(p string, d fs.DirEntry, err error) error {
				if err != nil {
					return err
				}
				if d.IsDir() {
					if p != root && (strings.HasPrefix(d.Name(), ".") || d.Name() == "vendor" || d.Name() == "testdata") {
						return filepath.SkipDir
					}
				} else if strings.HasSuffix(d.Name(), "_test.oak") {
					dirs[filepath.Dir(p)] = true
				}
				return nil
			})
			if err != nil {
				return nil, err
			}
		} else {
			info, err := os.Stat(path)
			if err != nil {
				return nil, err
			}
			if !info.IsDir() {
				return nil, fmt.Errorf("oak test expects a directory or ./..., got %s", path)
			}
			dirs[path] = true
		}
	}
	canonical := map[string]bool{}
	for dir := range dirs {
		abs, err := filepath.Abs(dir)
		if err != nil {
			return nil, err
		}
		canonical[abs] = true
	}
	names := make([]string, 0, len(canonical))
	for dir := range canonical {
		names = append(names, dir)
	}
	sort.Strings(names)
	var packages []Package
	for _, dir := range names {
		entries, err := os.ReadDir(dir)
		if err != nil {
			return nil, err
		}
		var pkg Package
		pkg.Dir = dir
		generators := map[string]*ast.FunctionStatement{}
		var src strings.Builder
		clauses := 0
		files := 0
		for _, entry := range entries {
			if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") || strings.HasPrefix(entry.Name(), ".") {
				continue
			}
			path := filepath.Join(dir, entry.Name())
			data, err := os.ReadFile(path)
			if err != nil {
				return nil, err
			}
			// A directory whose files open with package clauses is a module
			// package: the compiler's loader assembles it, not concatenation.
			files++
			if name := packageClause(string(data)); name != "" {
				if clauses != 0 && name != pkg.Name {
					return nil, fmt.Errorf("%s: package clause %q disagrees with %q", path, name, pkg.Name)
				}
				pkg.Name, pkg.Module = name, true
				clauses++
			}
			// Newlines prevent final comments/layout blocks from eating the next file.
			fmt.Fprintf(&src, "\n// oak test source: %s\n%s\n", entry.Name(), data)
			if !strings.HasSuffix(entry.Name(), "_test.oak") {
				continue
			}
			tree, err := compiler.New().WithSource(path, string(data)).Parse().Get()
			if err != nil {
				return nil, fmt.Errorf("%s: %w", path, err)
			}
			for _, stmt := range tree.Root.Statements {
				fn, ok := stmt.(*ast.FunctionStatement)
				if !ok || fn.Name == nil {
					continue
				}
				kind := testKind(fn.Name.Value)
				if strings.HasPrefix(fn.Name.Value, "Generate") && testKind(strings.TrimPrefix(fn.Name.Value, "Generate")) != "" {
					if _, exists := generators[fn.Name.Value]; exists {
						return nil, fmt.Errorf("duplicate generator %s", fn.Name.Value)
					}
					generators[fn.Name.Value] = fn
				}
				if kind == "" {
					continue
				}
				if err := validateTest(fn, kind); err != nil {
					return nil, fmt.Errorf("%s:%d: %w", path, fn.Token.Line, err)
				}
				pkg.Tests = append(pkg.Tests, Test{Name: fn.Name.Value, File: entry.Name(), Line: fn.Token.Line, Kind: kind})
			}
		}
		if clauses != 0 && clauses != files {
			return nil, fmt.Errorf("%s: every file of a module package must begin with the same package clause", dir)
		}
		pkg.Source = src.String()
		sort.Slice(pkg.Tests, func(i, j int) bool { return pkg.Tests[i].Name < pkg.Tests[j].Name })
		for i := 1; i < len(pkg.Tests); i++ {
			if pkg.Tests[i-1].Name == pkg.Tests[i].Name {
				return nil, fmt.Errorf("duplicate test %s in %s", pkg.Tests[i].Name, dir)
			}
		}
		for i := range pkg.Tests {
			name := "Generate" + pkg.Tests[i].Name
			if fn := generators[name]; fn != nil {
				if pkg.Tests[i].Kind != "property" && pkg.Tests[i].Kind != "simulation" {
					return nil, fmt.Errorf("%s: command generators require a Property or Sim target", name)
				}
				if err := validateTest(fn, "generator"); err != nil {
					return nil, err
				}
				pkg.Tests[i].Generator = name
				delete(generators, name)
			}
		}
		if len(generators) != 0 {
			return nil, fmt.Errorf("command generator has no registered target in %s", dir)
		}
		pkg.Registry = append([]Test(nil), pkg.Tests...)
		for _, test := range pkg.Tests {
			if test.Generator != "" {
				pkg.Registry = append(pkg.Registry, Test{Name: test.Generator, Kind: "generator"})
			}
		}
		if len(pkg.Tests) != 0 {
			packages = append(packages, pkg)
		}
	}
	return packages, nil
}

func testKind(name string) string {
	for _, p := range []struct{ prefix, kind string }{{"Property", "property"}, {"Fuzz", "fuzz"}, {"Sim", "simulation"}, {"Test", "unit"}} {
		if strings.HasPrefix(name, p.prefix) && len(name) > len(p.prefix) {
			next := name[len(p.prefix)]
			if next == '_' || next >= 'A' && next <= 'Z' {
				return p.kind
			}
		}
	}
	return ""
}

func validateTest(fn *ast.FunctionStatement, kind string) error {
	bad := func() error {
		return fmt.Errorf("%s must be a non-generic %s test returning (), with %s", fn.Name.Value, kind, map[bool]string{true: "no arguments", false: "one []u8 argument"}[kind == "unit"])
	}
	if !cIdentifier.MatchString(fn.Name.Value) || fn.Receiver != nil || len(fn.TypeParams) != 0 || fn.ExternSymbol != "" {
		return bad()
	}
	ret, ok := fn.ReturnType.(*ast.Identifier)
	if !ok || ret.Value != "()" {
		return bad()
	}
	if kind == "unit" {
		if len(fn.Parameters) != 0 {
			return bad()
		}
		return nil
	}
	if len(fn.Parameters) != 1 || fn.Parameters[0].Variadic {
		return bad()
	}
	view, ok := fn.Parameters[0].Type.(*ast.IndexExpression)
	if !ok || view.Dot {
		return bad()
	}
	element, eok := view.Left.(*ast.Identifier)
	marker, mok := view.Index.(*ast.Identifier)
	if !eok || !mok || element.Value != "u8" || marker.Value != "" {
		return bad()
	}
	return nil
}
