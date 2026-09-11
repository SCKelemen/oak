package main

// Module subcommands with go-tool counterparts: `oak mod init`, `graph`,
// `why`, and `edit` (docs/spec/115-tooling.md). All are offline and edit
// oak.mod, when they do, line by line through a temporary file and rename.

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
)

// modInit creates oak.mod for a new module; it never overwrites one.
func modInit(args []string) int {
	if len(args) == 0 || len(args) > 2 {
		fmt.Fprintln(os.Stderr, "usage: oak mod init <module-path> [dir]")
		return 2
	}
	path, dir := args[0], "."
	if len(args) == 2 {
		dir = args[1]
	}
	if err := modules.ValidateImportPath(path); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod init: %v\n", err)
		return 1
	}
	if modules.IsStandardLibraryPath(path) {
		fmt.Fprintf(os.Stderr, "oak mod init: module path %q is reserved for the standard library (first segment needs a dot)\n", path)
		return 1
	}
	manifest := filepath.Join(dir, modules.ManifestFile)
	if _, err := os.Stat(manifest); err == nil {
		fmt.Fprintf(os.Stderr, "oak mod init: %s already exists\n", manifest)
		return 1
	}
	text := fmt.Sprintf("module %s\noak 0.1.0\n", path)
	if _, err := modules.ParseManifest(text); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod init: %v\n", err)
		return 1
	}
	if err := os.WriteFile(manifest, []byte(text), 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod init: %v\n", err)
		return 1
	}
	fmt.Printf("created %s: module %s\n", manifest, path)
	return 0
}

// modGraph prints the requirement graph reachable from the module: one
// `module requirement@version` line per edge, root first, from the manifests
// the loader locates (replace directives and the module cache).
func modGraph(args []string) int {
	dir := "."
	if len(args) > 0 {
		dir = args[0]
	}
	manifest, err := readManifest(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod graph: %v\n", err)
		return 1
	}
	graph, err := compiler.RequirementGraph(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod graph: %v\n", err)
		return 1
	}
	printed := map[string]bool{}
	var visit func(path string)
	visit = func(path string) {
		if printed[path] {
			return
		}
		printed[path] = true
		for _, requirement := range graph[path] {
			fmt.Printf("%s %s@%s\n", path, requirement.Path, requirement.Version)
		}
		for _, requirement := range graph[path] {
			visit(requirement.Path)
		}
	}
	visit(manifest.Path)
	return 0
}

// modWhy shows, for an import path, which packages of the module import it,
// as import chains from a module package to the target.
func modWhy(args []string) int {
	if len(args) == 0 || len(args) > 2 {
		fmt.Fprintln(os.Stderr, "usage: oak mod why <import-path> [dir]")
		return 2
	}
	target, dir := args[0], "."
	if len(args) == 2 {
		dir = args[1]
	}
	manifest, packages, err := compiler.ModulePackages(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod why: %v\n", err)
		return 1
	}
	paths := make([]string, 0, len(packages))
	for path := range packages {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	found := false
	for _, path := range paths {
		tree, err := compiler.New().WithPackageDir(packages[path]).Parse().Get()
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod why: %s: %v\n", path, err)
			return 1
		}
		chain := importChain(tree.Modules.Imports, path, target, manifest.Path)
		if chain == nil {
			continue
		}
		found = true
		fmt.Printf("# %s\n%s\n", path, strings.Join(chain, "\n"))
	}
	if !found {
		fmt.Printf("(no package of %s imports %s)\n", manifest.Path, target)
		return 1
	}
	return 0
}

// importChain finds a shortest import chain from `from` to any package that
// is the target or has it as a module-path prefix.
func importChain(edges map[string][]string, from, target, module string) []string {
	type node struct {
		path string
		via  []string
	}
	matches := func(path string) bool {
		return path == target || modules.HasPathPrefix(path, target)
	}
	queue := []node{{from, []string{from}}}
	seen := map[string]bool{from: true}
	for len(queue) != 0 {
		current := queue[0]
		queue = queue[1:]
		if matches(current.path) && current.path != from {
			return current.via
		}
		for _, next := range edges[current.path] {
			if seen[next] {
				continue
			}
			seen[next] = true
			queue = append(queue, node{next, append(append([]string(nil), current.via...), next)})
		}
	}
	return nil
}

// modEdit rewrites oak.mod directives line by line: -require p@v adds or
// replaces a require, -droprequire p removes one (and its replace),
// -replace p=>dir sets a replace, -dropreplace p removes one, -version v and
// -profile p set those directives. The result must parse before it is
// written.
func modEdit(args []string) int {
	dir := "."
	type edit struct{ kind, a, b string }
	var edits []edit
	for i := 0; i < len(args); i++ {
		flag := args[i]
		switch {
		case (flag == "-require" || flag == "-droprequire" || flag == "-replace" || flag == "-dropreplace" || flag == "-version" || flag == "-profile") && i+1 < len(args):
			value := args[i+1]
			i++
			switch flag {
			case "-require":
				path, version, ok := strings.Cut(value, "@")
				if !ok {
					fmt.Fprintf(os.Stderr, "oak mod edit: -require takes path@version, got %q\n", value)
					return 2
				}
				edits = append(edits, edit{"require", path, version})
			case "-replace":
				path, target, ok := strings.Cut(value, "=>")
				if !ok {
					fmt.Fprintf(os.Stderr, "oak mod edit: -replace takes path=>dir, got %q\n", value)
					return 2
				}
				edits = append(edits, edit{"replace", strings.TrimSpace(path), strings.TrimSpace(target)})
			default:
				edits = append(edits, edit{strings.TrimPrefix(flag, "-"), value, ""})
			}
		case strings.HasPrefix(flag, "-"):
			fmt.Fprintf(os.Stderr, "oak mod edit: unknown flag %s\nusage: oak mod edit [-require p@v] [-droprequire p] [-replace p=>dir] [-dropreplace p] [-version v] [-profile p] [dir]\n", flag)
			return 2
		default:
			dir = flag
		}
	}
	if len(edits) == 0 {
		fmt.Fprintln(os.Stderr, "oak mod edit: nothing to do")
		return 2
	}
	manifestPath := filepath.Join(dir, modules.ManifestFile)
	text, err := os.ReadFile(manifestPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod edit: %v\n", err)
		return 1
	}
	lines := strings.Split(strings.TrimRight(string(text), "\n"), "\n")
	for _, e := range edits {
		switch e.kind {
		case "require":
			if _, err := packageapi.ParseVersion(e.b); err != nil {
				fmt.Fprintf(os.Stderr, "oak mod edit: %v\n", err)
				return 1
			}
			lines = setDirective(lines, "require", e.a, fmt.Sprintf("require %s %s", e.a, e.b))
		case "droprequire":
			lines = dropDirective(lines, "require", e.a)
			lines = dropDirective(lines, "replace", e.a)
		case "replace":
			lines = setDirective(lines, "replace", e.a, fmt.Sprintf("replace %s => %s", e.a, e.b))
		case "dropreplace":
			lines = dropDirective(lines, "replace", e.a)
		case "version", "profile":
			lines = setDirective(lines, e.kind, "", fmt.Sprintf("%s %s", e.kind, e.a))
		}
	}
	rewritten := strings.Join(lines, "\n") + "\n"
	if _, err := modules.ParseManifest(rewritten); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod edit: the edited manifest does not parse: %v\n", err)
		return 1
	}
	if err := replaceFile(manifestPath, rewritten); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod edit: %v\n", err)
		return 1
	}
	fmt.Printf("rewrote %s\n", manifestPath)
	return 0
}

// setDirective replaces the line `directive key ...` (or the only
// `directive ...` line when key is "") with line, appending when absent.
func setDirective(lines []string, directive, key, line string) []string {
	for i, existing := range lines {
		fields := strings.Fields(existing)
		if len(fields) == 0 || fields[0] != directive {
			continue
		}
		if key == "" || (len(fields) > 1 && fields[1] == key) {
			lines[i] = line
			return lines
		}
	}
	return append(lines, line)
}

// dropDirective removes every `directive key ...` line.
func dropDirective(lines []string, directive, key string) []string {
	var kept []string
	for _, existing := range lines {
		fields := strings.Fields(existing)
		if len(fields) > 1 && fields[0] == directive && fields[1] == key {
			continue
		}
		kept = append(kept, existing)
	}
	return kept
}

// replaceFile writes text over path through a temporary file in the same
// directory and a rename.
func replaceFile(path, text string) error {
	temp, err := os.CreateTemp(filepath.Dir(path), "."+filepath.Base(path)+".*")
	if err != nil {
		return err
	}
	tempPath := temp.Name()
	if _, err := temp.WriteString(text); err != nil {
		temp.Close()
		os.Remove(tempPath)
		return err
	}
	if err := temp.Close(); err != nil {
		os.Remove(tempPath)
		return err
	}
	if err := os.Rename(tempPath, path); err != nil {
		os.Remove(tempPath)
		return errors.Join(err)
	}
	return nil
}
