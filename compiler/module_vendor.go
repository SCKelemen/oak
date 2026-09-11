package compiler

// `oak mod vendor` (docs/spec/83-modules.md section 4.3, docs/spec/
// 115-tooling.md): copy the modules a build would locate — through replace
// directives and the module cache, at the versions minimal version selection
// picks — into <root>/vendor/<module path>/, so the module builds from its
// own tree with neither. Only regular files are copied and every destination
// is checked to lie under the vendor directory.

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
)

// VendoredModule is one module `oak mod vendor` copied.
type VendoredModule struct {
	Path    string
	Version string
	Source  string
	Files   int
}

// Vendor copies every dependency module of the module at moduleDir into its
// vendor directory and writes vendor/modules.txt. An existing vendor
// directory is replaced.
func Vendor(moduleDir string) ([]VendoredModule, error) {
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
	graph, err := RequirementGraph(root)
	if err != nil {
		return nil, err
	}
	var requirements []modules.Requirement
	for _, edges := range graph {
		requirements = append(requirements, edges...)
	}
	selected := modules.Select(requirements)
	cache := os.Getenv("OAKMODCACHE")
	vendorDir := filepath.Join(root, modules.VendorDir)
	staging, err := os.MkdirTemp(root, ".vendor-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(staging)
	var vendored []VendoredModule
	for _, path := range modules.SelectedPaths(selected) {
		version := selected[path]
		source, err := locateForVendor(root, manifest, cache, path, version)
		if err != nil {
			return nil, err
		}
		destination := filepath.Join(staging, filepath.FromSlash(path))
		count, err := copyModuleTree(source, destination, staging)
		if err != nil {
			return nil, fmt.Errorf("vendor %s: %w", path, err)
		}
		vendored = append(vendored, VendoredModule{Path: path, Version: version.String(), Source: source, Files: count})
	}
	var list strings.Builder
	for _, module := range vendored {
		fmt.Fprintf(&list, "# %s %s\n", module.Path, module.Version)
	}
	if err := os.WriteFile(filepath.Join(staging, modules.VendorListFile), []byte(list.String()), 0o644); err != nil {
		return nil, err
	}
	if err := os.RemoveAll(vendorDir); err != nil {
		return nil, err
	}
	if err := os.Rename(staging, vendorDir); err != nil {
		return nil, err
	}
	return vendored, nil
}

// locateForVendor finds a module's directory as a build would, ignoring an
// existing vendor copy (the point is to refresh it).
func locateForVendor(root string, manifest modules.Manifest, cache, path string, version packageapi.Version) (string, error) {
	if replacement, replaced := manifest.Replaces[path]; replaced {
		dir := replacement
		if !filepath.IsAbs(dir) {
			dir = filepath.Join(root, filepath.FromSlash(dir))
		}
		return filepath.Abs(dir)
	}
	if cache == "" {
		return "", fmt.Errorf("module %s v%s: no replace directive and no module cache ($OAKMODCACHE) provide it", path, version)
	}
	dir := modules.CacheDir(cache, path, version)
	if info, err := os.Stat(filepath.Join(dir, modules.ManifestFile)); err != nil || info.IsDir() {
		return "", fmt.Errorf("module %s v%s is not in the module cache; run oak mod download", path, version)
	}
	return dir, nil
}

// copyModuleTree copies the module's regular files (sources, manifest,
// api.json) from source to destination, skipping hidden entries, vendor and
// testdata directories, download records, and anything that is not a
// regular file. Every destination path must lie under within.
func copyModuleTree(source, destination, within string) (int, error) {
	count := 0
	err := filepath.WalkDir(source, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		rel, err := filepath.Rel(source, path)
		if err != nil {
			return err
		}
		name := entry.Name()
		if entry.IsDir() {
			if rel != "." && (strings.HasPrefix(name, ".") || name == modules.VendorDir || name == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if strings.HasPrefix(name, ".") || !entry.Type().IsRegular() {
			return nil
		}
		if !strings.HasSuffix(name, ".oak") && name != modules.ManifestFile && name != modules.APIFile {
			return nil
		}
		target := filepath.Join(destination, rel)
		if inside, err := filepath.Rel(within, target); err != nil || inside == ".." || strings.HasPrefix(inside, ".."+string(filepath.Separator)) {
			return fmt.Errorf("%s escapes the vendor directory", rel)
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		if err := os.MkdirAll(filepath.Dir(target), 0o755); err != nil {
			return err
		}
		if err := os.WriteFile(target, data, 0o644); err != nil {
			return err
		}
		count++
		return nil
	})
	return count, err
}
