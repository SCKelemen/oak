package main

// `oak doc`, `oak fmt`, `oak mod vendor`, `oak mod verify`
// (docs/spec/115-tooling.md).

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
)

// docCommand prints the public declarations of a module's packages (or of
// one package with -package) with their canonical types, from the same API
// snapshot the semver tooling uses; an optional name filters the listing.
func docCommand(args []string) int {
	dir, packageName, name := ".", "", ""
	var positional []string
	fs := newFlagSet("doc", "oak doc [-package P] [dir] [name]")
	fs.StringVar(&packageName, "package", "", "document one package under this import path")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	positional = rest
	for _, arg := range positional {
		if info, err := os.Stat(arg); err == nil && info.IsDir() {
			dir = arg
			continue
		}
		name = arg
	}
	var snapshots []packageapi.Snapshot
	if packageName != "" {
		one, err := compiler.New().WithPackageName(packageName).WithPackageDir(dir).APISnapshot("0.0.0").Get()
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak doc: %v\n", err)
			return 1
		}
		snapshots = append(snapshots, one)
	} else {
		module, err := compiler.ModuleAPISnapshot(dir, "0.0.0")
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak doc: %v\n", err)
			return 1
		}
		paths := make([]string, 0, len(module.Packages))
		for path := range module.Packages {
			paths = append(paths, path)
		}
		sort.Strings(paths)
		for _, path := range paths {
			snapshots = append(snapshots, module.Packages[path])
		}
	}
	shown := 0
	for _, snapshot := range snapshots {
		names := make([]string, 0, len(snapshot.Exports))
		for exported := range snapshot.Exports {
			if name == "" || exported == name || strings.HasSuffix(exported, "::"+name) {
				names = append(names, exported)
			}
		}
		if len(names) == 0 {
			continue
		}
		sort.Strings(names)
		fmt.Printf("package %s\n", snapshot.Package)
		for _, exported := range names {
			export := snapshot.Exports[exported]
			switch export.Kind {
			case "function", "method":
				fmt.Printf("    pub %s: %s\n", exported, export.Type)
			case "value":
				fmt.Printf("    pub %s: %s\n", exported, export.Type)
			case "opaque type":
				fmt.Printf("    pub(opaque) %s: type\n", exported)
			default:
				fmt.Printf("    pub %s: type = %s\n", exported, export.Type)
			}
			shown++
		}
		fmt.Println()
	}
	if shown == 0 {
		if name != "" {
			fmt.Fprintf(os.Stderr, "oak doc: no public declaration named %q\n", name)
		} else {
			fmt.Println("(no public declarations)")
		}
		return 1
	}
	return 0
}

// fmtCommand canonicalizes whitespace: CRLF to LF, trailing whitespace
// removed, runs of blank lines collapsed to one, exactly one final newline.
// A file is rewritten only when the result parses to the same syntax tree,
// so formatting can never change a program's meaning; a file that does not
// parse is reported and left alone. Without -l or -w, the formatted text is
// printed.
func fmtCommand(args []string) int {
	list, write := false, false
	fs := newFlagSet("fmt", "oak fmt [-l] [-w] [file.oak|dir|pattern]...")
	fs.BoolVar(&list, "l", false, "list files whose formatting differs")
	fs.BoolVar(&write, "w", false, "write the result back to the files")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	var paths []string
	for _, arg := range rest {
		if isPattern(arg) {
			root := strings.TrimSuffix(strings.TrimSuffix(arg, "..."), "/")
			if root == "" {
				root = "."
			}
			arg = root
		}
		paths = append(paths, arg)
	}
	if len(paths) == 0 {
		paths = []string{"."}
	}
	var files []string
	for _, path := range paths {
		info, err := os.Stat(path)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak fmt: %v\n", err)
			return 1
		}
		if !info.IsDir() {
			files = append(files, path)
			continue
		}
		err = filepath.WalkDir(path, func(current string, entry os.DirEntry, walkErr error) error {
			if walkErr != nil {
				return walkErr
			}
			if entry.IsDir() {
				if current != path && (strings.HasPrefix(entry.Name(), ".") || entry.Name() == modules.VendorDir) {
					return filepath.SkipDir
				}
				return nil
			}
			if strings.HasSuffix(entry.Name(), ".oak") {
				files = append(files, current)
			}
			return nil
		})
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak fmt: %v\n", err)
			return 1
		}
	}
	status := 0
	for _, file := range files {
		original, err := os.ReadFile(file)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak fmt: %v\n", err)
			status = 1
			continue
		}
		formatted := canonicalWhitespace(original)
		if !write && !list {
			os.Stdout.Write(formatted)
			continue
		}
		if bytes.Equal(formatted, original) {
			continue
		}
		if err := sameSyntax(file, original, formatted); err != nil {
			fmt.Fprintf(os.Stderr, "oak fmt: %s left alone: %v\n", file, err)
			status = 1
			continue
		}
		if list {
			fmt.Println(file)
		}
		if write {
			if err := replaceFile(file, string(formatted)); err != nil {
				fmt.Fprintf(os.Stderr, "oak fmt: %v\n", err)
				status = 1
			}
		}
	}
	return status
}

// canonicalWhitespace applies the formatting rules to a file's bytes.
func canonicalWhitespace(text []byte) []byte {
	normalized := strings.ReplaceAll(string(text), "\r\n", "\n")
	lines := strings.Split(normalized, "\n")
	var out []string
	blank := 0
	for _, line := range lines {
		trimmed := strings.TrimRight(line, " \t")
		if trimmed == "" {
			blank++
			if blank > 1 {
				continue
			}
			out = append(out, "")
			continue
		}
		blank = 0
		out = append(out, trimmed)
	}
	for len(out) != 0 && out[len(out)-1] == "" {
		out = out[:len(out)-1]
	}
	if len(out) == 0 {
		return []byte{}
	}
	return []byte(strings.Join(out, "\n") + "\n")
}

// sameSyntax parses both texts through the front end and requires identical
// trees (and a parseable original).
func sameSyntax(name string, original, formatted []byte) error {
	before, err := compiler.New().WithSource(name, string(original)).Parse().Get()
	if err != nil {
		return fmt.Errorf("does not parse: %v", err)
	}
	after, err := compiler.New().WithSource(name, string(formatted)).Parse().Get()
	if err != nil {
		return fmt.Errorf("formatted text does not parse: %v", err)
	}
	if before.Root.String() != after.Root.String() {
		return fmt.Errorf("formatting would change the syntax tree")
	}
	return nil
}

// modVendor copies the module's dependencies into vendor/.
func modVendor(args []string) int {
	dir := "."
	if len(args) > 0 {
		dir = args[0]
	}
	vendored, err := compiler.Vendor(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod vendor: %v\n", err)
		return 1
	}
	for _, module := range vendored {
		fmt.Printf("vendored %s %s (%d files) from %s\n", module.Path, module.Version, module.Files, module.Source)
	}
	if len(vendored) == 0 {
		fmt.Println("nothing to vendor")
	}
	return 0
}

// modVerify checks cached requirements against their download records.
func modVerify(args []string) int {
	dir := "."
	if len(args) > 0 {
		dir = args[0]
	}
	manifest, err := readManifest(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod verify: %v\n", err)
		return 1
	}
	cache := os.Getenv("OAKMODCACHE")
	if cache == "" {
		fmt.Fprintln(os.Stderr, "oak mod verify: OAKMODCACHE is not set; nothing to verify")
		return 1
	}
	results := modules.VerifyCache(cache, manifest)
	status := 0
	for _, result := range results {
		if result.State == "ok" {
			continue
		}
		status = 1
		fmt.Printf("%s %s: %s", result.Path, result.Version, result.State)
		if result.Detail != "" {
			fmt.Printf(" (%s)", result.Detail)
		}
		fmt.Println()
	}
	if status == 0 {
		fmt.Printf("all %d cached module(s) verified\n", len(results))
	}
	return status
}
