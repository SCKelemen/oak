package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"os/user"
	"path"
	"path/filepath"
	"runtime"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
	"github.com/SCKelemen/oak/repl"
	"github.com/SCKelemen/oak/testrunner"
)

func main() {
	if len(os.Args) < 2 {
		startREPL()
		return
	}
	name, args := os.Args[1], os.Args[2:]
	switch name {
	case "test":
		os.Exit(testrunner.Main(args, os.Stdout, os.Stderr))
	case "repl":
		startREPL()
		return
	case "protocol":
		os.Exit(protocolCommand(args, os.Stdout, os.Stderr))
	case "-h", "-help", "--help":
		printUsage(os.Stdout)
		return
	}
	if c := findCommand(name); c != nil && c.run != nil {
		os.Exit(c.run(args))
	}
	if strings.HasSuffix(name, ".oak") {
		// Compile mode: oak file.oak writes file.c beside the source.
		os.Exit(compileFile(name))
	}
	fmt.Fprintf(os.Stderr, "oak %s: unknown command\n", name)
	fmt.Fprintln(os.Stderr, "Run 'oak help' for usage.")
	os.Exit(2)
}

// compileFile is the original single-file mode: `oak file.oak` emits C beside
// the source.
func compileFile(filename string) int {
	source, err := os.ReadFile(filename)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak: %v\n", err)
		return 1
	}
	output, err := compiler.New().WithSource(filename, string(source)).EmitC().Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	outputFile := strings.TrimSuffix(filename, ".oak") + ".c"
	if err := os.WriteFile(outputFile, []byte(output), 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "oak: %v\n", err)
		return 1
	}
	fmt.Printf("Compiled %s -> %s\n", filename, outputFile)
	return 0
}

// startREPL runs the interactive session.
func startREPL() {
	usr, err := user.Current()
	if err != nil {
		panic(err)
	}
	fmt.Printf("Hello %s, welcome to Oak 🌳\n", usr.Username)
	fmt.Printf("Type Oak code or 'exit' to quit\n")
	repl.Start(os.Stdin, os.Stdout)
}

// reportAsmVerdict prints the assembler's verification verdicts
// (docs/spec/94-assembler.md §8) — proven, witness-checked, or trusted —
// which never reject a build but are the reader's evidence that an asm
// unit matches its Oak fallback body. Mismatches are errors and arrive
// through the compilation's error instead.
func reportAsmVerdict(d *diagnostic.Diagnostic) {
	if (d.Source == "asm" || d.Source == "native") && d.Severity == diagnostic.SeverityInformation {
		fmt.Fprintf(os.Stderr, "%s: %s\n", d.Source, d.Message)
	}
}

// buildPackage implements `oak build [-o out] [-emit-c] [dir|file.oak]`
// (docs/spec/115-tooling.md): the package at dir
// (default ".") and everything it imports, resolved through the enclosing
// module's oak.mod (docs/spec/83-modules.md), compile to one C translation
// unit, which the system C compiler turns into an executable named after the
// package (or `-o out`); `-emit-c`, or an `-o` ending in .c, writes the C.
func buildPackage(args []string) int {
	output, header, leanOut, profile := "", "", "", ""
	lines, emitC, nativeBodies := false, false, false
	asmMode := defaultAsmMode()
	fs := newFlagSet("build", "oak build [-o out] [-emit-c] [-header out.h] [-lean out.lean] [-profile default|strict] [-asm native|c] [-native] [-lines] [dir|file.oak|pattern]...")
	fs.StringVar(&output, "o", "", "output file: an executable, or C when it ends in .c")
	fs.BoolVar(&emitC, "emit-c", false, "write C instead of an executable")
	fs.StringVar(&header, "header", "", "write the C header of the exported surface (docs/spec/92-ffi.md section 2.6)")
	fs.StringVar(&leanOut, "lean", "", "write the Lean 4 extraction of the package (docs/spec/95-extraction.md)")
	fs.StringVar(&profile, "profile", "", "discipline profile: default or strict (docs/spec/85-discipline.md)")
	fs.StringVar(&asmMode, "asm", asmMode, "asm units: native (Oak assembler companion object) or c (inline __asm__; docs/spec/94-assembler.md section 9)")
	fs.BoolVar(&lines, "lines", false, "emit #line directives so C diagnostics point at Oak source")
	fs.BoolVar(&nativeBodies, "native", false, "lower Oak bodies through the native backend where its subset reaches (docs/spec/94-assembler.md section 9)")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	if !validProfile(profile) {
		fmt.Fprintf(os.Stderr, "oak build: unknown profile %q (default or strict; docs/spec/85-discipline.md section 1)\n", profile)
		return 2
	}
	if asmMode != "native" && asmMode != "c" {
		fmt.Fprintf(os.Stderr, "oak build: -asm takes native or c, got %q\n", asmMode)
		return 2
	}
	targets, err := expandPackagePatterns(rest)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
		return 1
	}
	if len(targets) > 1 && (output != "" || header != "" || leanOut != "") {
		fmt.Fprintln(os.Stderr, "oak build: -o, -header, and -lean apply to a single package")
		return 2
	}
	for _, dir := range targets {
		if code := buildOne(dir, output, header, leanOut, profile, asmMode, lines, emitC, nativeBodies); code != 0 {
			return code
		}
	}
	return 0
}

// buildOne builds a single package or file.
func buildOne(dir, output, header, leanOut, profile, asmMode string, lines, emitC, nativeBodies bool) int {
	comp, err := compilationFor(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
		return 1
	}
	comp = comp.WithProfile(profile).WithDiagnosticSink(reportAsmVerdict)
	if lines {
		comp = comp.WithLineDirectives()
	}
	if nativeBodies {
		comp = comp.WithNativeBodies()
	}
	if strings.HasSuffix(output, ".c") {
		emitC = true
	}
	code, err := comp.EmitC().Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	if leanOut != "" {
		extracted, err := comp.EmitLean("Oak." + leanNamespace(dir)).Get()
		if err != nil {
			fmt.Fprintf(os.Stderr, "%v\n", err)
			return 1
		}
		if err := os.WriteFile(leanOut, []byte(extracted), 0o644); err != nil {
			fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
			return 1
		}
	}
	if header != "" {
		api, err := comp.EmitHeader().Get()
		if err != nil {
			fmt.Fprintf(os.Stderr, "%v\n", err)
			return 1
		}
		if err := os.WriteFile(header, []byte(api), 0o644); err != nil {
			fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
			return 1
		}
	}
	if output == "" {
		abs, err := filepath.Abs(dir)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
			return 1
		}
		output = strings.TrimSuffix(filepath.Base(abs), ".oak")
		if info, statErr := os.Stat(dir); statErr == nil && info.IsDir() {
			if name, nameErr := executableName(dir); nameErr == nil {
				output = name
			}
		}
		if emitC {
			output += ".c"
		}
	}
	if emitC {
		if err := os.WriteFile(output, []byte(code), 0o644); err != nil {
			fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
			return 1
		}
		fmt.Printf("Built %s -> %s\n", dir, output)
		return 0
	}
	// An executable, like `go build`: the emitted C compiled by the system
	// C compiler into the named output, through the build cache.
	_, object, err := emitForHost(comp, asmMode)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	inputs, err := comp.LinkInputs()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	cached, err := compileC(code, object, inputs, output)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
		return 1
	}
	if cached {
		fmt.Printf("Built %s -> %s (cached)\n", dir, output)
		return 0
	}
	fmt.Printf("Built %s -> %s\n", dir, output)
	return 0
}

// modCommand implements the module tooling (docs/spec/82-package-semver.md
// sections 6-8, docs/spec/83-modules.md section 4.4):
//
//	oak mod download [dir]            fetch pinned requirements into $OAKMODCACHE,
//	                                  verifying digests and carried api.json
//	oak mod api [dir]                 print the module's API snapshot (JSON)
//	oak mod api -package P [-version V] <dir|file.oak>
//	                                  snapshot one package (a directory or a
//	                                  single source file)
//	oak mod diff previous.json [dir|current.json]
//	                                  classify the API change since previous.json
//	                                  (module or package snapshots)
//	oak mod bump previous.json [dir|current.json]
//	                                  print the required version; with a
//	                                  `version` directive (or a current
//	                                  snapshot), enforce it
//	oak mod compat dep-api.json [dir] check sealed imports against a
//	                                  dependency's snapshot
//	oak mod pack [-o out.tar.gz] [-previous prev.json] [-url location] [dir]
//	                                  build the module archive carrying api.json
//	                                  and print its `require` line
//	oak mod tidy [-w] [dir]          reconcile require directives with imports;
//	                                  -w rewrites oak.mod
//	oak mod try path candidate-dir [-dir dir]
//	                                  build every package with `path` replaced
//	                                  by a local candidate: decides unsealed imports
//	oak mod upgrade [-dir dir] dep-api.json...
//	                                  pick the highest candidate version whose
//	                                  snapshot satisfies the module's sealed imports
//
// The compiler itself never fetches; every input here is a local file.
func modCommand(args []string) int {
	if len(args) == 0 || args[0] == "help" {
		printModUsage(os.Stderr)
		return 2
	}
	switch args[0] {
	case "init":
		return modInit(args[1:])
	case "graph":
		return modGraph(args[1:])
	case "why":
		return modWhy(args[1:])
	case "edit":
		return modEdit(args[1:])
	case "vendor":
		return modVendor(args[1:])
	case "verify":
		return modVerify(args[1:])
	case "download":
		return modDownload(args[1:])
	case "api":
		return modAPI(args[1:])
	case "diff":
		return modDiff(args[1:], false)
	case "bump":
		return modDiff(args[1:], true)
	case "compat":
		return modCompat(args[1:])
	case "pack":
		return modPack(args[1:])
	case "upgrade":
		return modUpgrade(args[1:])
	case "try":
		return modTry(args[1:])
	case "tidy":
		return modTidy(args[1:])
	}
	fmt.Fprintf(os.Stderr, "oak mod: unknown subcommand %q\n", args[0])
	printModUsage(os.Stderr)
	return 2
}

// printModUsage lists the module subcommands.
func printModUsage(out io.Writer) {
	fmt.Fprintln(out, "usage: oak mod <subcommand> [args]")
	fmt.Fprintln(out)
	for _, line := range []string{
		"init <module-path> [dir]         create oak.mod",
		"download [dir]                   fetch pinned requirements into $OAKMODCACHE",
		"tidy [-w] [dir]                  reconcile require directives with imports",
		"edit [-require p@v] [-droprequire p] [-replace p=>dir] [-dropreplace p] [-version v] [-profile p] [dir]",
		"                                 rewrite oak.mod directives",
		"vendor [dir]                     copy dependencies into vendor/ (builds then need no cache)",
		"verify [dir]                     check cached dependencies against their download records",
		"graph [dir]                      print the module requirement graph",
		"why <import-path> [dir]          show which packages import a path",
		"api [dir] | api -package P [-version V] <dir|file>",
		"                                 print an API snapshot (JSON)",
		"diff previous.json [dir|cur.json] classify the API change",
		"bump previous.json [dir|cur.json] enforce the exact required version",
		"compat dep-api.json [dir]        check sealed imports against a snapshot",
		"pack [-o out.tar.gz] [-previous prev.json] [-url location] [dir]",
		"                                 build the module archive",
		"upgrade [-dir dir] dep-api.json... pick the highest compatible candidate",
		"try path candidate-dir [-dir dir] build against a local candidate",
	} {
		fmt.Fprintf(out, "\t%s\n", line)
	}
}

func modDownload(args []string) int {
	dir := "."
	if len(args) > 0 {
		dir = args[0]
	}
	manifest, err := readManifest(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	fetcher := &modules.Fetcher{
		Cache:  os.Getenv("OAKMODCACHE"),
		Log:    func(format string, args ...interface{}) { fmt.Printf(format+"\n", args...) },
		Verify: compiler.VerifyArchiveAPI,
	}
	if err := fetcher.Download(context.Background(), manifest); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	return 0
}

func modAPI(args []string) int {
	dir, packageName, packageVersion := ".", "", ""
	fs := newFlagSet("mod api", "oak mod api [dir] | oak mod api -package P [-version V] <dir|file.oak>")
	fs.StringVar(&packageName, "package", "", "snapshot one package under this import path")
	fs.StringVar(&packageVersion, "version", "", "version to record in a single-package snapshot (default 0.0.0)")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	if len(rest) > 0 {
		dir = rest[0]
	}
	if packageName != "" {
		return modAPIPackage(packageName, packageVersion, dir)
	}
	manifest, err := readManifest(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	version := manifest.Version
	if version == "" {
		version = "0.0.0"
	}
	snapshot, err := compiler.ModuleAPISnapshot(dir, version)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	encoder := json.NewEncoder(os.Stdout)
	encoder.SetEscapeHTML(false)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(snapshot); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	return 0
}

// modAPIPackage snapshots a single package — a directory built through the
// module loader or one source file — the former `oak-api` tool.
func modAPIPackage(name, version, target string) int {
	if version == "" {
		version = "0.0.0"
	}
	comp := compiler.New().WithPackageName(name)
	if info, err := os.Stat(target); err == nil && info.IsDir() {
		comp = comp.WithPackageDir(target)
	} else {
		source, err := os.ReadFile(target)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod api: %v\n", err)
			return 1
		}
		comp = comp.WithSource(target, string(source))
	}
	snapshot, err := comp.APISnapshot(version).Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod api: %v\n", err)
		return 1
	}
	encoder := json.NewEncoder(os.Stdout)
	encoder.SetEscapeHTML(false)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(snapshot); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod api: %v\n", err)
		return 1
	}
	return 0
}

func modDiff(args []string, enforce bool) int {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: oak mod diff|bump previous.json [dir]")
		return 2
	}
	dir := "."
	if len(args) > 1 {
		dir = args[1]
	}
	previous, err := compiler.ReadModuleSnapshot(args[0])
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	// The current API is the module at dir, or a second snapshot file (the
	// former `oak-semver` form); with a file, its version is the declared
	// candidate.
	var current packageapi.ModuleSnapshot
	declared := ""
	if info, statErr := os.Stat(dir); statErr == nil && !info.IsDir() {
		current, err = compiler.ReadModuleSnapshot(dir)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
			return 1
		}
		declared = current.Version
	} else {
		manifest, err := readManifest(dir)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
			return 1
		}
		declared = manifest.Version
		candidate := declared
		if candidate == "" {
			candidate = previous.Version
		}
		current, err = compiler.ModuleAPISnapshot(dir, candidate)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
			return 1
		}
	}
	required, report, err := packageapi.RequiredVersion(previous, current)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	for _, pkg := range report.Packages {
		if pkg.Reason != "" {
			fmt.Printf("%s: %s (%s)\n", pkg.Package, pkg.Reason, pkg.Level)
		}
		for _, change := range pkg.Changes {
			fmt.Printf("%s: %s: %s (%s)\n", pkg.Package, change.Name, change.Reason, change.Level)
		}
	}
	fmt.Printf("required change: %s; required version: %s\n", report.Required, required)
	if !enforce {
		return 0
	}
	if declared == "" {
		fmt.Fprintf(os.Stderr, "oak mod bump: add `version %s` to %s\n", required, modules.ManifestFile)
		return 1
	}
	if _, err := packageapi.EnforceModule(previous, current); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod bump: %v\n", err)
		return 1
	}
	fmt.Printf("version %s is the exact required bump\n", declared)
	return 0
}

func modCompat(args []string) int {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: oak mod compat dep-api.json [dir]")
		return 2
	}
	dir := "."
	if len(args) > 1 {
		dir = args[1]
	}
	snapshot, err := compiler.ReadModuleSnapshot(args[0])
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	problems, err := compiler.CheckSealedCompatibility(dir, snapshot)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	for _, problem := range problems {
		fmt.Println(problem.String())
	}
	if len(problems) != 0 {
		fmt.Printf("%d sealed member(s) incompatible with %s %s\n", len(problems), snapshot.Module, snapshot.Version)
		return 1
	}
	fmt.Printf("every sealed import of %s is satisfied by %s\n", snapshot.Module, snapshot.Version)
	return 0
}

// modPack builds the archive `oak mod download` consumes (docs/spec/
// 82-package-semver.md section 7): the module's files under one
// `<name>-<version>/` wrapper plus api.json, the snapshot at the manifest's
// `version`. With -previous the exact-bump rule is enforced first, so an
// archive whose version lies about its API change is never produced.
func modPack(args []string) int {
	dir, output, previousPath, location := ".", "", "", "<url>"
	fs := newFlagSet("mod pack", "oak mod pack [-o out.tar.gz] [-previous prev.json] [-url location] [dir]")
	fs.StringVar(&output, "o", "", "archive to write (default <name>-<version>.tar.gz)")
	fs.StringVar(&previousPath, "previous", "", "previous snapshot; the exact bump is enforced before packing")
	fs.StringVar(&location, "url", "<url>", "HTTPS location to print in the require line")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	if len(rest) > 0 {
		dir = rest[0]
	}
	manifest, err := readManifest(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
		return 1
	}
	if manifest.Version == "" {
		fmt.Fprintf(os.Stderr, "oak mod pack: %s declares no `version`; a packed module must name the version it publishes\n", modules.ManifestFile)
		return 1
	}
	if location != "<url>" {
		if err := modules.ValidateLocation(location); err != nil {
			fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
			return 1
		}
	}
	snapshot, err := compiler.ModuleAPISnapshot(dir, manifest.Version)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
		return 1
	}
	if previousPath != "" {
		previous, err := compiler.ReadModuleSnapshot(previousPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
			return 1
		}
		if _, err := packageapi.EnforceModule(previous, snapshot); err != nil {
			fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
			return 1
		}
	}
	api, err := json.MarshalIndent(snapshot, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
		return 1
	}
	wrapper := path.Base(manifest.Path) + "-" + manifest.Version
	archive, digest, err := modules.Pack(dir, wrapper, api)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
		return 1
	}
	if output == "" {
		output = wrapper + ".tar.gz"
	}
	if err := os.WriteFile(output, archive, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod pack: %v\n", err)
		return 1
	}
	fmt.Printf("wrote %s (%d bytes, %d packages)\n", output, len(archive), len(snapshot.Packages))
	fmt.Printf("require %s %s %s %s\n", manifest.Path, manifest.Version, location, digest)
	return 0
}

// modUpgrade picks, among candidate snapshots of one dependency, the highest
// version whose API satisfies every sealed import of the module
// (docs/spec/82-package-semver.md section 8). Every input is a local file.
func modUpgrade(args []string) int {
	dir := "."
	var files []string
	fs := newFlagSet("mod upgrade", "oak mod upgrade [-dir dir] dep-api.json...")
	fs.StringVar(&dir, "dir", ".", "module directory")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	files = rest
	if len(files) == 0 {
		fmt.Fprintln(os.Stderr, "usage: oak mod upgrade [-dir dir] dep-api.json...")
		return 2
	}
	candidates := make([]packageapi.ModuleSnapshot, 0, len(files))
	for _, file := range files {
		snapshot, err := compiler.ReadModuleSnapshot(file)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak mod upgrade: %v\n", err)
			return 1
		}
		candidates = append(candidates, snapshot)
	}
	best, results, err := compiler.HighestCompatible(dir, candidates)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod upgrade: %v\n", err)
		return 1
	}
	for _, result := range results {
		if len(result.Problems) == 0 {
			fmt.Printf("%s %s: compatible\n", result.Snapshot.Module, result.Snapshot.Version)
			continue
		}
		fmt.Printf("%s %s: %d incompatible sealed member(s)\n", result.Snapshot.Module, result.Snapshot.Version, len(result.Problems))
		for _, problem := range result.Problems {
			fmt.Printf("  %s\n", problem)
		}
	}
	if best == nil {
		fmt.Fprintf(os.Stderr, "oak mod upgrade: no candidate satisfies the module's sealed imports\n")
		return 1
	}
	fmt.Printf("require %s %s\n", best.Module, best.Version)
	return 0
}

// modTry decides the unsealed imports of a module against a local candidate
// of a dependency by building (docs/spec/82-package-semver.md section 8).
func modTry(args []string) int {
	dir := "."
	var positional []string
	fs := newFlagSet("mod try", "oak mod try path candidate-dir [-dir dir]")
	fs.StringVar(&dir, "dir", ".", "module directory")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	positional = rest
	if len(positional) != 2 {
		fmt.Fprintln(os.Stderr, "usage: oak mod try path candidate-dir [-dir dir]")
		return 2
	}
	results, err := compiler.TryReplacement(dir, positional[0], positional[1])
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod try: %v\n", err)
		return 1
	}
	failed := 0
	for _, result := range results {
		if result.Err == nil {
			fmt.Printf("%s: compatible\n", result.Package)
			continue
		}
		failed++
		fmt.Printf("%s: incompatible\n  %s\n", result.Package, strings.ReplaceAll(strings.TrimSpace(result.Err.Error()), "\n", "\n  "))
	}
	if failed != 0 {
		fmt.Printf("%d of %d package(s) do not build against %s\n", failed, len(results), positional[1])
		return 1
	}
	fmt.Printf("every package builds against %s\n", positional[1])
	return 0
}

// modTidy reconciles require directives with the module's imports
// (docs/spec/83-modules.md section 4.5). Without -w it reports; with -w it
// rewrites oak.mod, dropping unused requires and adding the missing ones
// the module cache ($OAKMODCACHE) can provide.
func modTidy(args []string) int {
	dir, write := ".", false
	fs := newFlagSet("mod tidy", "oak mod tidy [-w] [dir]")
	fs.BoolVar(&write, "w", false, "rewrite oak.mod")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	if len(rest) > 0 {
		dir = rest[0]
	}
	report, err := compiler.Tidy(dir, os.Getenv("OAKMODCACHE"))
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod tidy: %v\n", err)
		return 1
	}
	for _, path := range report.Unused {
		fmt.Printf("unused: require %s (no package imports from it)\n", path)
	}
	for _, missing := range report.Missing {
		version := missing.Version
		if version == "" {
			version = "<version unknown>"
		}
		fmt.Printf("missing: require %s %s (imported: %s)\n", missing.Path, version, strings.Join(missing.Imports, ", "))
	}
	for _, path := range report.Uncovered {
		fmt.Printf("uncovered: import %q matches no require or replace; add the module that provides it\n", path)
	}
	if report.Clean() {
		fmt.Println("oak.mod is tidy")
		return 0
	}
	if !write {
		fmt.Println("run `oak mod tidy -w` to rewrite oak.mod")
		return 1
	}
	if err := compiler.TidyWrite(dir, report); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod tidy: %v\n", err)
		return 1
	}
	fmt.Printf("rewrote %s\n", filepath.Join(dir, modules.ManifestFile))
	unresolved := len(report.Uncovered)
	for _, missing := range report.Missing {
		if missing.Version == "" {
			unresolved++
		}
	}
	if unresolved != 0 {
		fmt.Printf("%d requirement(s) still need a version or module path by hand\n", unresolved)
		return 1
	}
	return 0
}

func readManifest(dir string) (modules.Manifest, error) {
	text, err := os.ReadFile(filepath.Join(dir, modules.ManifestFile))
	if err != nil {
		return modules.Manifest{}, err
	}
	return modules.ParseManifest(string(text))
}

// validProfile accepts the discipline profiles of docs/spec/85-discipline.md
// section 1; "" selects the default profile.
func validProfile(profile string) bool {
	return profile == "" || profile == "default" || profile == "strict"
}

// runPackage implements `oak run [-profile p] [dir]`: build the package through the module
// loader, compile the emitted C with the system C compiler into a temporary
// directory, execute the binary with this process's stdio, and propagate its
// exit status. This is a development convenience over trusted local source,
// not a sandbox.
func runPackage(args []string) int {
	dir := "."
	profile := ""
	asmMode := defaultAsmMode()
	own, programArgs := splitProgramArgs(args)
	nativeBodies := false
	fs := newFlagSet("run", "oak run [-profile default|strict] [-asm native|c] [-native] [dir] [-- program arguments]")
	fs.StringVar(&profile, "profile", "", "discipline profile: default or strict")
	fs.StringVar(&asmMode, "asm", asmMode, "asm units: native or c (docs/spec/94-assembler.md section 9)")
	fs.BoolVar(&nativeBodies, "native", false, "lower Oak bodies through the native backend where its subset reaches (docs/spec/94-assembler.md section 9)")
	rest, exit, stop := parseFlags(fs, own)
	if stop {
		return exit
	}
	if len(rest) > 1 {
		fmt.Fprintln(os.Stderr, "oak run: one package directory; pass program arguments after --")
		return 2
	}
	if len(rest) == 1 {
		dir = rest[0]
	}
	if !validProfile(profile) {
		fmt.Fprintf(os.Stderr, "oak run: unknown profile %q (default or strict; docs/spec/85-discipline.md section 1)\n", profile)
		return 2
	}
	if asmMode != "native" && asmMode != "c" {
		fmt.Fprintf(os.Stderr, "oak run: -asm takes native or c, got %q\n", asmMode)
		return 2
	}
	comp := compiler.New().WithPackageDir(dir).WithProfile(profile).WithDiagnosticSink(reportAsmVerdict)
	if nativeBodies {
		comp = comp.WithNativeBodies()
	}
	code, object, err := emitForHost(comp, asmMode)
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	work, err := os.MkdirTemp("", "oak-run-")
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak run: %v\n", err)
		return 1
	}
	defer os.RemoveAll(work)
	binary := filepath.Join(work, "program")
	inputs, err := comp.LinkInputs()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	if _, err := compileC(code, object, inputs, binary); err != nil {
		fmt.Fprintf(os.Stderr, "oak run: %v\n", err)
		return 1
	}
	program := exec.Command(binary, programArgs...)
	program.Stdin, program.Stdout, program.Stderr = os.Stdin, os.Stdout, os.Stderr
	if err := program.Run(); err != nil {
		var exitErr *exec.ExitError
		if errors.As(err, &exitErr) {
			return exitErr.ExitCode()
		}
		fmt.Fprintf(os.Stderr, "oak run: %v\n", err)
		return 1
	}
	return 0
}

// defaultAsmMode: asm units are encoded by the Oak assembler on AArch64
// hosts (where `oak run` executes them) and assembled by the C toolchain
// elsewhere, since the companion object must match the running machine.
func defaultAsmMode() string {
	if runtime.GOARCH == "arm64" && (runtime.GOOS == "darwin" || runtime.GOOS == "linux") {
		return "native"
	}
	return "c"
}

// emitForHost emits the C and, in native mode, the asm units' companion
// object for the host's object format.
func emitForHost(comp compiler.Compilation, asmMode string) (string, []byte, error) {
	if asmMode == "native" {
		native, err := comp.EmitNative(compiler.HostObjectFormat()).Get()
		if err != nil {
			return "", nil, err
		}
		return native.C, native.Object, nil
	}
	code, err := comp.EmitC().Get()
	return code, nil, err
}

// leanNamespace derives a Lean namespace component from a package
// directory: its base name capitalized, with every character outside the
// identifier alphabet spelled as an underscore.
func leanNamespace(dir string) string {
	abs, err := filepath.Abs(dir)
	if err != nil {
		abs = dir
	}
	var out strings.Builder
	for i, r := range filepath.Base(abs) {
		switch {
		case r >= 'a' && r <= 'z':
			if i == 0 {
				r -= 'a' - 'A'
			}
			out.WriteRune(r)
		case (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9' && i > 0):
			out.WriteRune(r)
		default:
			out.WriteByte('_')
		}
	}
	if out.Len() == 0 {
		return "Package"
	}
	return out.String()
}
