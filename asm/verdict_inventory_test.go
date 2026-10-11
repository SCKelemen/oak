package asm

import (
	"go/ast"
	"go/parser"
	"go/token"
	"io/fs"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"testing"
	"testing/fstest"
)

// This is a review inventory, not a sealed proof kernel or a type checker.
// Verdict remains public. Record every direct proven/dynamic construction and
// direct assignment of VerdictProven in the maintained source-directory scope,
// including consumers outside package asm.
// Function-level counts make a new site require a deliberate inventory review.
func TestVerdictAuthorityInventory(t *testing.T) {
	want := map[string]int{
		"asm/effects.go:decideSpans:proven":       2, // result and span-memory conjunction
		"asm/effects.go:decideEffects:proven":     1, // no state or span writes on either side
		"asm/loops.go:verifyLoopsWith:proven":     1, // coupling, effects and loop trap domains
		"asm/verify.go:decideCells:proven":        2, // result and package-state conjunction
		"asm/verify.go:decideEqual:proven":        5, // linear/structural/branch decisions
		"asm/verify.go:blastEqual:proven":         1, // BDD decision
		"asm/verdict.go:composeProvenPair:proven": 1, // both complete input proofs, exact callee union
		// Cache framing/kind/dependency checks restore a trusted record; they
		// do not reconstruct or freshly check its mathematical derivation.
		"compiler/verdict_cache.go:cachedVerdict:dynamic": 1,
	}
	paths, err := verdictInventorySourcePaths(os.DirFS(".."), verdictInventorySourceDirs)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]int{}
	for _, path := range paths {
		file, err := parser.ParseFile(token.NewFileSet(), filepath.Join("..", filepath.FromSlash(path)), nil, 0)
		if err != nil {
			t.Fatal(err)
		}
		for site, count := range verdictAuthoritySites(file, path) {
			got[site] += count
		}
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("proof authority inventory changed; audit each new or removed site before updating\ngot: %#v\nwant: %#v", got, want)
	}
}

func verdictAuthoritySites(file *ast.File, path string) map[string]int {
	local := filepath.Dir(path) == "asm"
	qualifiers := map[string]bool{}
	for _, imp := range file.Imports {
		name, _ := strconv.Unquote(imp.Path.Value)
		if name != "github.com/SCKelemen/oak/asm" {
			continue
		}
		qualifier := "asm"
		if imp.Name != nil {
			qualifier = imp.Name.Name
		}
		if qualifier == "." {
			local = true
		} else {
			qualifiers[qualifier] = true
		}
	}
	isName := func(expr ast.Expr, name string) bool {
		switch expr := expr.(type) {
		case *ast.Ident:
			return local && expr.Name == name
		case *ast.SelectorExpr:
			pkg, ok := expr.X.(*ast.Ident)
			return ok && qualifiers[pkg.Name] && expr.Sel.Name == name
		}
		return false
	}
	got := map[string]int{}
	for _, decl := range file.Decls {
		owner := "<package>"
		if fn, ok := decl.(*ast.FuncDecl); ok {
			owner = fn.Name.Name
		}
		record := func(kind string) { got[path+":"+owner+":"+kind]++ }
		ast.Inspect(decl, func(node ast.Node) bool {
			switch node := node.(type) {
			case *ast.CompositeLit:
				if !isName(node.Type, "Verdict") {
					break
				}
				for _, elem := range node.Elts {
					field, ok := elem.(*ast.KeyValueExpr)
					if !ok {
						record("positional")
						break
					}
					key, ok := field.Key.(*ast.Ident)
					if !ok || key.Name != "Kind" {
						continue
					}
					if isName(field.Value, "VerdictProven") {
						record("proven")
					} else if !isName(field.Value, "VerdictTrusted") && !isName(field.Value, "VerdictWitnessed") && !isName(field.Value, "VerdictMismatch") {
						record("dynamic")
					}
				}
			case *ast.AssignStmt:
				for _, rhs := range node.Rhs {
					if isName(rhs, "VerdictProven") {
						record("assignment")
					}
				}
			case *ast.ValueSpec:
				for _, value := range node.Values {
					if isName(value, "VerdictProven") {
						record("binding")
					}
				}
			}
			return true
		})
	}
	return got
}

func TestVerdictAuthorityInventoryDetectsNewSites(t *testing.T) {
	for _, qualifier := range []string{"asm", "proof", "."} {
		prefix := qualifier + "."
		if qualifier == "." {
			prefix = ""
		}
		source := `package consumer
import ` + qualifier + ` "github.com/SCKelemen/oak/asm"
func mint() {
 a := ` + prefix + `Verdict{Kind: ` + prefix + `VerdictProven}
 b := ` + prefix + `Verdict{Kind: restoredKind}
 c := ` + prefix + `Verdict{` + prefix + `VerdictProven, "", false, nil}
 a.Kind = ` + prefix + `VerdictProven
 var k = ` + prefix + `VerdictProven
 _ = b; _ = c; _ = k
}`
		file, err := parser.ParseFile(token.NewFileSet(), "consumer.go", source, 0)
		if err != nil {
			t.Fatal(err)
		}
		got := verdictAuthoritySites(file, "consumer/consumer.go")
		want := map[string]int{}
		for _, kind := range []string{"proven", "dynamic", "positional", "assignment", "binding"} {
			want["consumer/consumer.go:mint:"+kind] = 1
		}
		if !reflect.DeepEqual(got, want) {
			t.Errorf("import %s: got %#v, want %#v", qualifier, got, want)
		}
	}
}

// Exact directories containing tracked production Go sources at 259bf5baa5b.
// Maintain this scope when adding a package. ReadDir is deliberately not
// recursive: build outputs, caches and unlisted subdirectories are never read.
// New source files in these directories are included without requiring Git,
// so the inventory also works in a source archive and before files are staged.
var verdictInventorySourceDirs = []string{
	".",
	".github/scripts/native_arm64",
	"asm",
	"asm/internal/armfeat",
	"asm/internal/isagen",
	"asm/internal/riscvgen",
	"asm/internal/sysreggen",
	"ast",
	"benchmarks/kernels/go",
	"benchmarks/native/emit",
	"benchmarks/native/exact_fma",
	"benchmarks/rings/goref",
	"benchmarks/state-machines/cross",
	"benchmarks/stdlib/goref",
	"borrowchecker",
	"buildcache",
	"cmd/generate_golden",
	"cmd/oak-browser",
	"cmd/verify_golden",
	"codegen",
	"codegen/lean",
	"codegen/metal",
	"codegen/metal/gpu",
	"compiler",
	"diagnostic",
	"discipline",
	"evaluator",
	"experiments/verification-poc",
	"experiments/verification-poc/frontend",
	"experiments/verification-poc/internal/lrat",
	"hostform",
	"internal/lrat",
	"internal/nativetiming",
	"internal/wasmtest",
	"layout",
	"lowering",
	"lsp",
	"lsp/server",
	"machine",
	"modules",
	"nativegen",
	"object",
	"opt",
	"optir",
	"packageapi",
	"parser",
	"playground",
	"prove",
	"repl",
	"resourceflow",
	"scanner",
	"semir",
	"serialize",
	"source",
	"spec/sail",
	"spec/tamarin/crypto",
	"stdlib",
	"target",
	"testrunner",
	"token",
	"toolchain",
	"typechecker",
	"util",
	"wasm",
	"wasm/check",
	"wasm/encoding",
}

func verdictInventorySourcePaths(root fs.FS, dirs []string) ([]string, error) {
	var paths []string
	for _, dir := range dirs {
		entries, err := verdictInventoryReadDir(root, dir)
		if err != nil {
			return nil, err
		}
		for _, entry := range entries {
			// Never follow a directory or symlink into an unreviewed tree.
			if !entry.Type().IsRegular() || !strings.HasSuffix(entry.Name(), ".go") || strings.HasSuffix(entry.Name(), "_test.go") {
				continue
			}
			path := entry.Name()
			if dir != "." {
				path = dir + "/" + path
			}
			paths = append(paths, path)
		}
	}
	return paths, nil
}

func TestVerdictAuthorityInventorySourceScope(t *testing.T) {
	root := fstest.MapFS{
		"main.go":                        &fstest.MapFile{},
		"main_test.go":                   &fstest.MapFile{},
		"asm/verdict.go":                 &fstest.MapFile{},
		"asm/new_source.go":              &fstest.MapFile{},
		"asm/verdict_test.go":            &fstest.MapFile{},
		"asm/link.go":                    &fstest.MapFile{Mode: fs.ModeSymlink},
		"asm/unlisted/generated.go":      &fstest.MapFile{},
		"build/generated.go":             &fstest.MapFile{},
		".lake/cache/generated.go":       &fstest.MapFile{},
		"cache/generated.go":             &fstest.MapFile{},
		"node_modules/generated.go":      &fstest.MapFile{},
		"new_package/requires_review.go": &fstest.MapFile{},
	}
	got, err := verdictInventorySourcePaths(root, []string{".", "asm"})
	if err != nil {
		t.Fatal(err)
	}
	want := []string{"main.go", "asm/new_source.go", "asm/verdict.go"}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("source scope = %v, want %v", got, want)
	}
}

// Inspect each path component before entering it; fs.ReadDir alone could follow
// a symlink used as one of the explicitly listed directories or its ancestors.
func verdictInventoryReadDir(root fs.FS, dir string) ([]fs.DirEntry, error) {
	entries, err := fs.ReadDir(root, ".")
	if err != nil || dir == "." {
		return entries, err
	}
	current := ""
	for _, component := range strings.Split(dir, "/") {
		found := false
		for _, entry := range entries {
			if entry.Name() == component && entry.IsDir() && entry.Type()&fs.ModeSymlink == 0 {
				found = true
				break
			}
		}
		if !found {
			return nil, &fs.PathError{Op: "inventory directory", Path: dir, Err: fs.ErrInvalid}
		}
		if current != "" {
			current += "/"
		}
		current += component
		entries, err = fs.ReadDir(root, current)
		if err != nil {
			return nil, err
		}
	}
	return entries, nil
}

func TestVerdictAuthorityInventoryRejectsDirectorySymlinks(t *testing.T) {
	root := fstest.MapFS{
		"linked":             &fstest.MapFile{Mode: fs.ModeSymlink, Data: []byte("cache")},
		"cache/generated.go": &fstest.MapFile{},
	}
	for _, dir := range []string{"linked", "linked/nested"} {
		if _, err := verdictInventorySourcePaths(root, []string{dir}); err == nil {
			t.Fatalf("source scope followed a symlink in %q", dir)
		}
	}
}
