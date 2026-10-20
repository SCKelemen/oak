// Command oak-architecture inventories source dependencies without compiling Oak.
// It scans all build-tag variants; edges are conservative source-level unions.
package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
)

var scope = []string{"asm", "compiler", "machine", "nativegen", "optir"}

type Edge struct {
	From  string
	To    string
	Files []string
}
type Package struct {
	Path            string
	ProductionFiles int
	TestFiles       int
	ProductionLines int
}
type FileSize struct {
	Path  string
	Lines int
}
type Duplicate struct {
	SHA256 string
	Sites  []string
}
type Inventory struct {
	Schema              int
	Method              string
	Scope               []string
	Packages            []Package
	ProductionEdges     []Edge
	TestEdges           []Edge
	ProductionClosure   []string
	DirectConsumers     []string
	Cycles              [][]string
	LargestFiles        []FileSize
	ExactBodyCandidates []Duplicate
}

func main() {
	root := flag.String("root", ".", "repository root")
	output := flag.String("out", "", "JSON output (default stdout)")
	flag.Parse()
	inventory, err := scan(*root)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	data, err := json.MarshalIndent(inventory, "", "  ")
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	data = append(data, '\n')
	if *output == "" {
		_, err = os.Stdout.Write(data)
	} else {
		err = os.WriteFile(*output, data, 0644)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

func scan(root string) (Inventory, error) {
	inv := Inventory{Schema: 1, Method: "Go AST; all build-tag variants; nested modules, vendor, hidden directories and testdata excluded; test imports separate; line counts include comments and blanks; exact function bodies >=20 lines are review candidates, not semantic equivalence", Scope: scope}
	moduleData, err := os.ReadFile(filepath.Join(root, "go.mod"))
	if err != nil {
		return inv, err
	}
	module := ""
	for _, line := range strings.Split(string(moduleData), "\n") {
		f := strings.Fields(line)
		if len(f) == 2 && f[0] == "module" {
			module = strings.Trim(f[1], "\"")
			break
		}
	}
	if module == "" {
		return inv, fmt.Errorf("missing module directive")
	}
	packages := map[string]*Package{}
	prod, tests := map[string]*Edge{}, map[string]*Edge{}
	duplicates := map[string][]string{}
	fset := token.NewFileSet()
	err = filepath.WalkDir(root, func(path string, entry os.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() {
			if path != root {
				if strings.HasPrefix(entry.Name(), ".") || entry.Name() == "vendor" || entry.Name() == "testdata" {
					return filepath.SkipDir
				}
				if _, err := os.Stat(filepath.Join(path, "go.mod")); err == nil {
					return filepath.SkipDir
				}
			}
			return nil
		}
		if !strings.HasSuffix(path, ".go") {
			return nil
		}
		relative, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		relative = filepath.ToSlash(relative)
		dir := filepath.ToSlash(filepath.Dir(relative))
		contents, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		file, err := parser.ParseFile(fset, path, contents, 0)
		if err != nil {
			return err
		}
		pkg := packages[dir]
		if pkg == nil {
			pkg = &Package{Path: dir}
			packages[dir] = pkg
		}
		test := strings.HasSuffix(path, "_test.go")
		lines := bytes.Count(contents, []byte("\n"))
		if len(contents) > 0 && contents[len(contents)-1] != '\n' {
			lines++
		}
		edges := prod
		from := dir
		if test {
			pkg.TestFiles++
			edges = tests
			if strings.HasSuffix(file.Name.Name, "_test") {
				from += "_test"
			}
		} else {
			pkg.ProductionFiles++
			pkg.ProductionLines += lines
		}
		for _, imp := range file.Imports {
			name, err := strconv.Unquote(imp.Path.Value)
			if err != nil {
				return err
			}
			if name == module {
				name = "."
			} else if strings.HasPrefix(name, module+"/") {
				name = strings.TrimPrefix(name, module+"/")
			} else {
				continue
			}
			key := from + "\x00" + name
			edge := edges[key]
			if edge == nil {
				edge = &Edge{From: from, To: name}
				edges[key] = edge
			}
			edge.Files = append(edge.Files, relative)
		}
		if !test && inScope(dir) {
			inv.LargestFiles = append(inv.LargestFiles, FileSize{relative, lines})
			for _, decl := range file.Decls {
				fn, ok := decl.(*ast.FuncDecl)
				if !ok || fn.Body == nil {
					continue
				}
				if fset.Position(fn.Body.End()).Line-fset.Position(fn.Body.Pos()).Line+1 < 20 {
					continue
				}
				var body bytes.Buffer
				if err := printer.Fprint(&body, fset, fn.Body); err != nil {
					return err
				}
				hash := fmt.Sprintf("%x", sha256.Sum256(body.Bytes()))
				site := fmt.Sprintf("%s:%d:%s", relative, fset.Position(fn.Pos()).Line, fn.Name.Name)
				duplicates[hash] = append(duplicates[hash], site)
			}
		}
		return nil
	})
	if err != nil {
		return inv, err
	}
	for _, p := range packages {
		inv.Packages = append(inv.Packages, *p)
	}
	sort.Slice(inv.Packages, func(i, j int) bool { return inv.Packages[i].Path < inv.Packages[j].Path })
	inv.ProductionEdges = sortedEdges(prod)
	inv.TestEdges = sortedEdges(tests)
	graph := map[string][]string{}
	for _, e := range inv.ProductionEdges {
		graph[e.From] = append(graph[e.From], e.To)
	}
	seen := map[string]bool{}
	var visit func(string)
	visit = func(node string) {
		if seen[node] {
			return
		}
		seen[node] = true
		for _, next := range graph[node] {
			visit(next)
		}
	}
	for _, p := range inv.Packages {
		if inScope(p.Path) {
			visit(p.Path)
		}
	}
	for node := range seen {
		inv.ProductionClosure = append(inv.ProductionClosure, node)
	}
	sort.Strings(inv.ProductionClosure)
	consumers := map[string]bool{}
	for _, e := range inv.ProductionEdges {
		if inScope(e.To) && !inScope(e.From) {
			consumers[e.From] = true
		}
	}
	for node := range consumers {
		inv.DirectConsumers = append(inv.DirectConsumers, node)
	}
	sort.Strings(inv.DirectConsumers)
	inv.Cycles = cycles(graph, inv.ProductionClosure)
	sort.Slice(inv.LargestFiles, func(i, j int) bool {
		a, b := inv.LargestFiles[i], inv.LargestFiles[j]
		if a.Lines == b.Lines {
			return a.Path < b.Path
		}
		return a.Lines > b.Lines
	})
	if len(inv.LargestFiles) > 20 {
		inv.LargestFiles = inv.LargestFiles[:20]
	}
	for hash, sites := range duplicates {
		if len(sites) > 1 {
			sort.Strings(sites)
			inv.ExactBodyCandidates = append(inv.ExactBodyCandidates, Duplicate{hash, sites})
		}
	}
	sort.Slice(inv.ExactBodyCandidates, func(i, j int) bool { return inv.ExactBodyCandidates[i].SHA256 < inv.ExactBodyCandidates[j].SHA256 })
	return inv, nil
}

func inScope(path string) bool {
	for _, p := range scope {
		if path == p || strings.HasPrefix(path, p+"/") {
			return true
		}
	}
	return false
}
func sortedEdges(edges map[string]*Edge) []Edge {
	result := []Edge{}
	for _, edge := range edges {
		sort.Strings(edge.Files)
		result = append(result, *edge)
	}
	sort.Slice(result, func(i, j int) bool {
		a, b := result[i], result[j]
		if a.From == b.From {
			return a.To < b.To
		}
		return a.From < b.From
	})
	return result
}

// Tarjan SCCs: report each cyclic component once, including self imports.
func cycles(graph map[string][]string, nodes []string) [][]string {
	next := 0
	index, low := map[string]int{}, map[string]int{}
	onStack := map[string]bool{}
	stack := []string{}
	result := [][]string{}
	var visit func(string)
	visit = func(v string) {
		next++
		index[v] = next
		low[v] = next
		stack = append(stack, v)
		onStack[v] = true
		for _, w := range graph[v] {
			if index[w] == 0 {
				visit(w)
				if low[w] < low[v] {
					low[v] = low[w]
				}
			} else if onStack[w] && index[w] < low[v] {
				low[v] = index[w]
			}
		}
		if low[v] != index[v] {
			return
		}
		component := []string{}
		for {
			w := stack[len(stack)-1]
			stack = stack[:len(stack)-1]
			onStack[w] = false
			component = append(component, w)
			if w == v {
				break
			}
		}
		cyclic := len(component) > 1
		for _, w := range graph[v] {
			if w == v {
				cyclic = true
			}
		}
		if cyclic {
			sort.Strings(component)
			result = append(result, component)
		}
	}
	for _, node := range nodes {
		if index[node] == 0 {
			visit(node)
		}
	}
	sort.Slice(result, func(i, j int) bool { return strings.Join(result[i], "\x00") < strings.Join(result[j], "\x00") })
	return result
}
