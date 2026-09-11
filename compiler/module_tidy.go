package compiler

// `oak mod tidy` (docs/spec/83-modules.md section 4.5): reconcile a module's
// `require` directives with what its packages actually import. The check is
// syntactic — every package file is parsed, never built — so it works on a
// module that does not yet compile, and it never contacts a registry: a
// missing module can be proposed only when the module cache holds it.

import (
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/stdlib"
)

// TidyReport is what `oak mod tidy` found.
type TidyReport struct {
	// Unused are require directives no package of the module imports from.
	Unused []string
	// Missing are modules some package imports from without a require,
	// found in the module cache: the module path and its highest cached
	// version.
	Missing []MissingRequire
	// Uncovered are import paths no require or replace accounts for; the
	// providing module cannot be inferred offline.
	Uncovered []string
}

// MissingRequire is a module a package imports from without a require.
type MissingRequire struct {
	Path    string
	Version string // "" when unknown
	Imports []string
}

// Clean reports whether the manifest already matches the imports.
func (r TidyReport) Clean() bool {
	return len(r.Unused) == 0 && len(r.Missing) == 0 && len(r.Uncovered) == 0
}

// Tidy compares the module's require directives with the external imports
// of every package (test files included). cache is the module cache
// ($OAKMODCACHE, "" for none): a module found there under some version can
// be proposed for an import no require covers.
func Tidy(moduleDir, cache string) (TidyReport, error) {
	manifest, packages, err := ModulePackages(moduleDir)
	if err != nil {
		return TidyReport{}, err
	}
	imports := map[string][]string{} // external import path -> importing packages
	for path, dir := range packages {
		entries, err := os.ReadDir(dir)
		if err != nil {
			return TidyReport{}, err
		}
		for _, entry := range entries {
			if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") || strings.HasPrefix(entry.Name(), ".") {
				continue
			}
			text, err := os.ReadFile(filepath.Join(dir, entry.Name()))
			if err != nil {
				return TidyReport{}, err
			}
			for _, imported := range importPaths(string(text)) {
				if !externalImport(imported, manifest.Path) {
					continue
				}
				imports[imported] = append(imports[imported], path)
			}
		}
	}

	report := TidyReport{}
	used := map[string]bool{}
	missing := map[string]*MissingRequire{}
	for imported := range imports {
		if required := longestPrefix(imported, requirePaths(manifest)); required != "" {
			used[required] = true
			continue
		}
		if cached := longestPrefix(imported, cachedPaths(cache)); cached != "" {
			entry := missing[cached]
			if entry == nil {
				entry = &MissingRequire{Path: cached, Version: highestCached(cache, cached)}
				missing[cached] = entry
			}
			entry.Imports = append(entry.Imports, imported)
			continue
		}
		report.Uncovered = append(report.Uncovered, imported)
	}
	for _, requirement := range manifest.Requires {
		if !used[requirement.Path] {
			report.Unused = append(report.Unused, requirement.Path)
		}
	}
	for _, entry := range missing {
		sort.Strings(entry.Imports)
		report.Missing = append(report.Missing, *entry)
	}
	sort.Slice(report.Missing, func(i, j int) bool { return report.Missing[i].Path < report.Missing[j].Path })
	sort.Strings(report.Unused)
	sort.Strings(report.Uncovered)
	return report, nil
}

// TidyWrite rewrites the module's oak.mod from a report: unused require
// lines are dropped and known missing modules are appended as
// `require path version`, every other line verbatim. The file is replaced
// through a temporary file in the same directory. Uncovered imports are
// left for the author and reported.
func TidyWrite(moduleDir string, report TidyReport) error {
	root, err := filepath.Abs(moduleDir)
	if err != nil {
		return err
	}
	manifestPath := filepath.Join(root, modules.ManifestFile)
	text, err := os.ReadFile(manifestPath)
	if err != nil {
		return err
	}
	unused := map[string]bool{}
	for _, path := range report.Unused {
		unused[path] = true
	}
	var kept []string
	for _, line := range strings.Split(strings.TrimRight(string(text), "\n"), "\n") {
		fields := strings.Fields(line)
		if len(fields) >= 2 && fields[0] == "require" && unused[fields[1]] {
			continue
		}
		kept = append(kept, line)
	}
	for _, entry := range report.Missing {
		if entry.Version == "" {
			continue
		}
		kept = append(kept, fmt.Sprintf("require %s %s", entry.Path, entry.Version))
	}
	rewritten := strings.Join(kept, "\n") + "\n"
	if _, err := modules.ParseManifest(rewritten); err != nil {
		return fmt.Errorf("rewritten manifest does not parse: %w", err)
	}
	temp, err := os.CreateTemp(root, ".oak.mod.*")
	if err != nil {
		return err
	}
	tempPath := temp.Name()
	if _, err := temp.WriteString(rewritten); err != nil {
		temp.Close()
		os.Remove(tempPath)
		return err
	}
	if err := temp.Close(); err != nil {
		os.Remove(tempPath)
		return err
	}
	if err := os.Rename(tempPath, manifestPath); err != nil {
		os.Remove(tempPath)
		return err
	}
	return nil
}

// importPaths parses a file and lists its import paths, in source order.
// Nested module bodies are included; parse errors yield what was parsed.
func importPaths(text string) []string {
	program := parser.New(scanner.New(text)).ParseProgram()
	var paths []string
	var walk func(statements []ast.Statement)
	walk = func(statements []ast.Statement) {
		for _, stmt := range statements {
			switch s := stmt.(type) {
			case *ast.ImportStatement:
				if s.Path != nil {
					paths = append(paths, s.Path.Value)
				}
			case *ast.ModuleDeclaration:
				if s.Body != nil {
					walk(s.Body.Statements)
				}
			}
		}
	}
	if program != nil {
		walk(program.Statements)
	}
	return paths
}

// externalImport reports whether an import path names a package outside
// the module and the standard library.
func externalImport(path, modulePath string) bool {
	if bootstrapImports[path] || modules.IsStandardLibraryPath(path) {
		return false
	}
	if _, isLibrary := stdlib.Packages[path]; isLibrary {
		return false
	}
	return !modules.HasPathPrefix(path, modulePath)
}

func requirePaths(manifest modules.Manifest) []string {
	paths := make([]string, 0, len(manifest.Requires))
	for _, requirement := range manifest.Requires {
		paths = append(paths, requirement.Path)
	}
	return paths
}

// longestPrefix returns the longest candidate that is a segment-wise prefix
// of path, or "".
func longestPrefix(path string, candidates []string) string {
	best := ""
	for _, candidate := range candidates {
		if modules.HasPathPrefix(path, candidate) && len(candidate) > len(best) {
			best = candidate
		}
	}
	return best
}

// cachedPaths lists the module paths present in the module cache, whose
// layout is `<cache>/<path>@v<version>` (modules.CacheDir).
func cachedPaths(cache string) []string {
	if cache == "" {
		return nil
	}
	seen := map[string]bool{}
	_ = filepath.WalkDir(cache, func(path string, entry os.DirEntry, err error) error {
		if err != nil || !entry.IsDir() {
			return nil
		}
		name := entry.Name()
		if at := strings.LastIndex(name, "@v"); at > 0 {
			rel, relErr := filepath.Rel(cache, filepath.Join(filepath.Dir(path), name[:at]))
			if relErr == nil {
				seen[filepath.ToSlash(rel)] = true
			}
			return filepath.SkipDir
		}
		return nil
	})
	paths := make([]string, 0, len(seen))
	for path := range seen {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	return paths
}

// highestCached returns the highest version of a module in the cache.
func highestCached(cache, modulePath string) string {
	dir := filepath.Join(cache, filepath.FromSlash(filepath.Dir(modulePath)))
	base := filepath.Base(modulePath)
	entries, err := os.ReadDir(dir)
	if err != nil {
		return ""
	}
	best, found := packageapi.Version{}, false
	for _, entry := range entries {
		if !entry.IsDir() || !strings.HasPrefix(entry.Name(), base+"@v") {
			continue
		}
		version, err := packageapi.ParseVersion(strings.TrimPrefix(entry.Name(), base+"@v"))
		if err != nil {
			continue
		}
		if !found || versionLess(best, version) {
			best, found = version, true
		}
	}
	if !found {
		return ""
	}
	return best.String()
}
