// Inventory discovers test roots which reach an ARM64 host guard, including
// through package-local test helpers. It parses Go rather than matching source
// text, so comments, embedded Oak/C and strings cannot invent helper calls.
package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
)

type Root struct {
	Package string `json:"package"`
	Test    string `json:"test"`
	File    string `json:"file"`
}
type SkipSite struct {
	File     string `json:"file"`
	Function string `json:"function"`
	Call     string `json:"call"`
}
type Inventory struct {
	Roots []Root     `json:"roots"`
	Skips []SkipSite `json:"skips"`
}
type function struct {
	name    string
	file    string
	calls   []string
	skips   []string
	guarded bool
	test    bool
}

func scanReferences(node ast.Node, runtimeName string, f *function) error {
	hasArch, hasARM, hasSkip := false, false, false
	var scanErr error
	ast.Inspect(node, func(n ast.Node) bool {
		if scanErr != nil {
			return false
		}
		switch value := n.(type) {
		case *ast.Ident:
			// Include references, not only calls: aliases, callbacks and tables must
			// not hide guarded helpers. Shadowed names may conservatively need review.
			f.calls = append(f.calls, value.Name)
		case *ast.SelectorExpr:
			if id, ok := value.X.(*ast.Ident); ok && id.Name == runtimeName && value.Sel.Name == "GOARCH" {
				hasArch = true
			}
		case *ast.BasicLit:
			if value.Kind == token.STRING {
				text, _ := strconv.Unquote(value.Value)
				if text == "arm64" {
					hasARM = true
				}
			}
		case *ast.CallExpr:
			if call, ok := value.Fun.(*ast.SelectorExpr); ok && (call.Sel.Name == "Skip" || call.Sel.Name == "Skipf" || call.Sel.Name == "SkipNow") {
				hasSkip = true
				var text bytes.Buffer
				if scanErr = format.Node(&text, token.NewFileSet(), value); scanErr == nil {
					f.skips = append(f.skips, text.String())
				}
			}
		}
		return true
	})
	f.guarded = f.guarded || (hasArch && hasARM && hasSkip)
	return scanErr
}

func fileFunctions(path string, source any) (string, []function, error) {
	file, err := parser.ParseFile(token.NewFileSet(), path, source, parser.ParseComments)
	if err != nil {
		return "", nil, err
	}
	runtimeName := "runtime"
	for _, imp := range file.Imports {
		if imp.Path.Value == `"runtime"` && imp.Name != nil {
			runtimeName = imp.Name.Name
		}
	}
	armFile := strings.HasSuffix(path, "_arm64_test.go") || strings.HasSuffix(path, "_arm64.go")
	for _, comment := range file.Comments {
		for _, line := range comment.List {
			// Composite/negated platform constraints require explicit inventory review,
			// never an automatic Linux waiver.
			if strings.HasPrefix(line.Text, "//go:build ") && strings.Contains(line.Text, "arm64") {
				armFile = true
			}
		}
	}
	var functions []function
	for _, decl := range file.Decls {
		// Initializers may contain both aliases and function literals with guards.
		if gen, ok := decl.(*ast.GenDecl); ok {
			for _, spec := range gen.Specs {
				value, ok := spec.(*ast.ValueSpec)
				if !ok {
					continue
				}
				for _, name := range value.Names {
					if name.Name == "_" {
						continue
					}
					f := function{name: name.Name, file: filepath.ToSlash(path), guarded: armFile}
					if err := scanReferences(value, runtimeName, &f); err != nil {
						return "", nil, err
					}
					functions = append(functions, f)
				}
			}
		}
		fn, ok := decl.(*ast.FuncDecl)
		if !ok || fn.Body == nil || fn.Name.Name == "init" {
			continue
		}
		f := function{name: fn.Name.Name, file: filepath.ToSlash(path), guarded: armFile}
		if fn.Recv != nil {
			var receiver bytes.Buffer
			if err := format.Node(&receiver, token.NewFileSet(), fn.Recv.List[0].Type); err != nil {
				return "", nil, err
			}
			f.name = "(" + receiver.String() + ")." + f.name
		}
		f.test = fn.Recv == nil && strings.HasPrefix(f.name, "Test") && fn.Type.Params != nil && len(fn.Type.Params.List) == 1
		if err := scanReferences(fn.Body, runtimeName, &f); err != nil {
			return "", nil, err
		}
		functions = append(functions, f)
	}
	return file.Name.Name, functions, nil
}

func discover(root string) (Inventory, error) {
	packages := map[string]map[string]function{}
	err := filepath.WalkDir(root, func(path string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if entry.IsDir() {
			if path != root && (strings.HasPrefix(entry.Name(), ".") || entry.Name() == "vendor" || entry.Name() == "external" || entry.Name() == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(path, "_test.go") {
			return nil
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		pkg, funcs, err := fileFunctions(rel, data)
		if err != nil {
			return err
		}
		key := filepath.ToSlash(filepath.Dir(rel)) + ":" + pkg
		if packages[key] == nil {
			packages[key] = map[string]function{}
		}
		for _, fn := range funcs {
			// Receiver-qualified method names preserve their skip sites without
			// confusing them with bare-identifier helper calls.
			if _, exists := packages[key][fn.name]; exists {
				return fmt.Errorf("duplicate test/helper %s in %s", fn.name, key)
			}
			packages[key][fn.name] = fn
		}
		return nil
	})
	if err != nil {
		return Inventory{}, err
	}
	var roots []Root
	var skips []SkipSite
	for key, funcs := range packages {
		guarded := map[string]bool{}
		targets := map[string][]string{}
		for name, fn := range funcs {
			reference := name
			if dot := strings.LastIndex(name, ")."); dot >= 0 {
				reference = name[dot+2:]
			}
			targets[reference] = append(targets[reference], name)
			for _, call := range fn.skips {
				skips = append(skips, SkipSite{fn.file, name, call})
			}
			guarded[name] = fn.guarded
		}
		for changed := true; changed; {
			changed = false
			for name, fn := range funcs {
				if guarded[name] {
					continue
				}
				for _, call := range fn.calls {
					// A method selector or method value may refer to any local
					// receiver with this name. Over-approximate rather than
					// let a new indirect call silently escape the host lane.
					for _, target := range targets[call] {
						if guarded[target] {
							guarded[name] = true
							changed = true
							break
						}
					}
					if guarded[name] {
						break
					}
				}
			}
		}
		for name, fn := range funcs {
			if fn.test && guarded[name] {
				pkg := strings.SplitN(key, ":", 2)[0]
				if pkg != "." {
					pkg = "./" + pkg
				}
				roots = append(roots, Root{pkg, name, fn.file})
			}
		}
	}
	sort.Slice(roots, func(i, j int) bool {
		if roots[i].Package != roots[j].Package {
			return roots[i].Package < roots[j].Package
		}
		return roots[i].Test < roots[j].Test
	})
	sort.Slice(skips, func(i, j int) bool {
		a, b := skips[i], skips[j]
		if a.File != b.File {
			return a.File < b.File
		}
		if a.Function != b.Function {
			return a.Function < b.Function
		}
		return a.Call < b.Call
	})
	return Inventory{roots, skips}, nil
}

func main() {
	root := "."
	if len(os.Args) == 2 {
		root = os.Args[1]
	} else if len(os.Args) != 1 {
		fmt.Fprintln(os.Stderr, "usage: inventory [repository]")
		os.Exit(2)
	}
	roots, err := discover(root)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	if err := enc.Encode(roots); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
