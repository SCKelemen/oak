package compiler

// Module-level API snapshots (docs/spec/82-package-semver.md section 6): the
// checked public API of every package in an oak.mod module, keyed by import
// path, produced through the ordinary package build so visibility, opacity,
// and the semantic gates apply exactly as they do when compiling.

import (
	"encoding/json"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
)

// ModulePackages lists the import paths and directories of every package in
// the module rooted at moduleDir (directories holding .oak files, excluding
// hidden directories, vendor, and testdata), in sorted path order.
func ModulePackages(moduleDir string) (modules.Manifest, map[string]string, error) {
	root, err := filepath.Abs(moduleDir)
	if err != nil {
		return modules.Manifest{}, nil, err
	}
	text, err := os.ReadFile(filepath.Join(root, modules.ManifestFile))
	if err != nil {
		return modules.Manifest{}, nil, fmt.Errorf("%s: %w", moduleDir, err)
	}
	manifest, err := modules.ParseManifest(string(text))
	if err != nil {
		return modules.Manifest{}, nil, err
	}
	packages := map[string]string{}
	err = filepath.WalkDir(root, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() {
			name := entry.Name()
			if path != root && (strings.HasPrefix(name, ".") || name == "vendor" || name == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(entry.Name(), ".oak") || strings.HasSuffix(entry.Name(), "_test.oak") {
			return nil
		}
		dir := filepath.Dir(path)
		rel, err := filepath.Rel(root, dir)
		if err != nil {
			return err
		}
		importPath := manifest.Path
		if rel != "." {
			importPath = manifest.Path + "/" + filepath.ToSlash(rel)
		}
		packages[importPath] = dir
		return nil
	})
	if err != nil {
		return manifest, nil, err
	}
	return manifest, packages, nil
}

// ModuleAPISnapshot snapshots every package of a module at the given
// version. Each package is built as a root package, so its declarations keep
// their source names and only pub declarations are projected.
func ModuleAPISnapshot(moduleDir, version string) (packageapi.ModuleSnapshot, error) {
	if _, err := packageapi.ParseVersion(version); err != nil {
		return packageapi.ModuleSnapshot{}, err
	}
	manifest, packages, err := ModulePackages(moduleDir)
	if err != nil {
		return packageapi.ModuleSnapshot{}, err
	}
	snapshot := packageapi.ModuleSnapshot{Module: manifest.Path, Version: version, Packages: map[string]packageapi.Snapshot{}}
	paths := make([]string, 0, len(packages))
	for path := range packages {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	for _, path := range paths {
		comp := New().WithPackageName(path).WithPackageDir(packages[path])
		model, err := comp.SemanticModel().Get()
		if err != nil {
			return packageapi.ModuleSnapshot{}, fmt.Errorf("package %s: %w", path, err)
		}
		one, err := buildAPISnapshot(path, version, model, comp.options)
		if err != nil {
			return packageapi.ModuleSnapshot{}, fmt.Errorf("package %s: %w", path, err)
		}
		snapshot.Packages[path] = one
		// Nested modules (83-modules.md section 3.5) are packages of the
		// module too: each is projected from its elaborated declarations,
		// spelled as a directory package would spell itself.
		nested, err := nestedAPISnapshots(model, version, comp.options)
		if err != nil {
			return packageapi.ModuleSnapshot{}, fmt.Errorf("package %s: %w", path, err)
		}
		for nestedPath, one := range nested {
			if _, dup := snapshot.Packages[nestedPath]; dup {
				return packageapi.ModuleSnapshot{}, fmt.Errorf("package %s is both a directory and a nested module", nestedPath)
			}
			snapshot.Packages[nestedPath] = one
		}
	}
	return snapshot, nil
}

// nestedAPISnapshots snapshots every nested module of a checked package.
// Their declarations carry internal names after elaboration; every emitted
// name and type is demangled and the module's own path prefix dropped, so
// `Box` reads as `Box` and another package's type as `path.Name`, exactly as
// in a root build. Instances of generic packages carry no separate API.
func nestedAPISnapshots(model *SemanticModel, version string, options Options) (map[string]packageapi.Snapshot, error) {
	out := map[string]packageapi.Snapshot{}
	if model.Tree == nil || model.Tree.Modules == nil {
		return out, nil
	}
	for _, nestedPath := range model.Tree.Modules.NestedModules {
		if strings.Contains(nestedPath, "@") {
			continue
		}
		program := &ast.Program{Statements: model.Tree.Modules.NestedDeclarations[nestedPath]}
		spell := func(text string) string { return dependencySpelling(text, nestedPath) }
		one, err := snapshotDeclarations(nestedPath, version, program, model.TypeChecker, options, spell)
		if err != nil {
			return nil, fmt.Errorf("nested module %s: %w", nestedPath, err)
		}
		out[nestedPath] = one
	}
	return out, nil
}

// ReadModuleSnapshot decodes a module API snapshot file, bounded in size so a
// hostile archive cannot make the decoder allocate without limit.
func ReadModuleSnapshot(path string) (packageapi.ModuleSnapshot, error) {
	const limit = 64 << 20
	info, err := os.Stat(path)
	if err != nil {
		return packageapi.ModuleSnapshot{}, err
	}
	if info.Size() > limit {
		return packageapi.ModuleSnapshot{}, fmt.Errorf("%s exceeds %d bytes", path, limit)
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return packageapi.ModuleSnapshot{}, err
	}
	// A module snapshot carries "packages"; a single-package snapshot
	// (`oak mod api -package`) carries "exports" and is read as a module of
	// one package, so the same diff and bump rules apply to both shapes.
	var shape struct {
		Packages json.RawMessage `json:"packages"`
		Exports  json.RawMessage `json:"exports"`
	}
	if err := json.Unmarshal(data, &shape); err != nil {
		return packageapi.ModuleSnapshot{}, fmt.Errorf("%s: %w", path, err)
	}
	if len(shape.Packages) == 0 && len(shape.Exports) != 0 {
		var one packageapi.Snapshot
		if err := json.Unmarshal(data, &one); err != nil {
			return packageapi.ModuleSnapshot{}, fmt.Errorf("%s: %w", path, err)
		}
		return packageapi.ModuleSnapshot{Module: one.Package, Version: one.Version, Packages: map[string]packageapi.Snapshot{one.Package: one}}, nil
	}
	var snapshot packageapi.ModuleSnapshot
	if err := json.Unmarshal(data, &snapshot); err != nil {
		return packageapi.ModuleSnapshot{}, fmt.Errorf("%s: %w", path, err)
	}
	return snapshot, nil
}

// VerifyArchiveAPI is the API-honesty check run by `oak mod download` on an
// extracted archive before it is installed (docs/spec/82-package-semver.md
// section 7): when the archive carries api.json, that snapshot must name the
// required version and equal the API the module's source actually exposes.
// An archive without api.json is accepted; the digest already pins its bytes.
func VerifyArchiveAPI(dir string, version packageapi.Version) error {
	carried, err := ReadModuleSnapshot(filepath.Join(dir, modules.APIFile))
	if os.IsNotExist(err) {
		return nil
	}
	if err != nil {
		return err
	}
	if carried.Version != version.String() {
		return fmt.Errorf("%s declares version %s, required %s", modules.APIFile, carried.Version, version)
	}
	actual, err := ModuleAPISnapshot(dir, version.String())
	if err != nil {
		return err
	}
	if !packageapi.SameAPI(carried, actual) {
		return fmt.Errorf("%s does not match the API the module's source exposes", modules.APIFile)
	}
	return nil
}

// TryResult is one package's outcome when built against a candidate.
type TryResult struct {
	Package string
	Err     error
}

// TryReplacement builds every package of the module at moduleDir with the
// dependency `path` replaced by the local module at candidateDir, deciding
// what no snapshot can: whether the module's unsealed imports of that
// dependency still compile (docs/spec/82-package-semver.md section 8). The
// candidate's oak.mod must declare `path`; the module's manifest is never
// rewritten and nothing is fetched.
func TryReplacement(moduleDir, path, candidateDir string) ([]TryResult, error) {
	candidate, err := filepath.Abs(candidateDir)
	if err != nil {
		return nil, err
	}
	text, err := os.ReadFile(filepath.Join(candidate, modules.ManifestFile))
	if err != nil {
		return nil, fmt.Errorf("candidate: %w", err)
	}
	manifest, err := modules.ParseManifest(string(text))
	if err != nil {
		return nil, fmt.Errorf("candidate: %w", err)
	}
	if manifest.Path != path {
		return nil, fmt.Errorf("candidate %s declares module %q, not %q", candidate, manifest.Path, path)
	}
	_, packages, err := ModulePackages(moduleDir)
	if err != nil {
		return nil, err
	}
	paths := make([]string, 0, len(packages))
	for p := range packages {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	results := make([]TryResult, 0, len(paths))
	for _, p := range paths {
		_, err := New().WithPackageDir(packages[p]).WithReplace(path, candidate).Check().Get()
		results = append(results, TryResult{Package: p, Err: err})
	}
	return results, nil
}

// RequirementGraph returns, for the module at moduleDir and every module
// its manifests reach, the require directives of each — the edges of the
// module graph `oak mod graph` prints. Modules are located as a build
// locates them (replace directives, then the module cache); a module that
// cannot be located contributes no edges.
func RequirementGraph(moduleDir string) (map[string][]modules.Requirement, error) {
	root, err := filepath.Abs(moduleDir)
	if err != nil {
		return nil, err
	}
	text, err := os.ReadFile(filepath.Join(root, modules.ManifestFile))
	if err != nil {
		return nil, err
	}
	manifest, err := modules.ParseManifest(string(text))
	if err != nil {
		return nil, err
	}
	cache := os.Getenv("OAKMODCACHE")
	graph := map[string][]modules.Requirement{manifest.Path: manifest.Requires}
	queue := append([]modules.Requirement(nil), manifest.Requires...)
	for len(queue) != 0 {
		requirement := queue[0]
		queue = queue[1:]
		if _, seen := graph[requirement.Path]; seen {
			continue
		}
		dir := ""
		if replacement, replaced := manifest.Replaces[requirement.Path]; replaced {
			dir = replacement
			if !filepath.IsAbs(dir) {
				dir = filepath.Join(root, filepath.FromSlash(dir))
			}
		} else if cache != "" {
			dir = modules.CacheDir(cache, requirement.Path, requirement.Version)
		}
		graph[requirement.Path] = nil
		if dir == "" {
			continue
		}
		depText, err := os.ReadFile(filepath.Join(dir, modules.ManifestFile))
		if err != nil {
			continue
		}
		dep, err := modules.ParseManifest(string(depText))
		if err != nil {
			continue
		}
		graph[requirement.Path] = dep.Requires
		queue = append(queue, dep.Requires...)
	}
	return graph, nil
}
