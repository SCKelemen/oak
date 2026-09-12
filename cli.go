package main

// The oak command (docs/spec/115-tooling.md): one binary with the shape of
// the go tool — `oak <command> [flags] [args]`, `oak help [command]` — over
// the compiler, the module system, the test runner, and the REPL. Every
// command is offline unless it says otherwise (`oak mod download`), external
// programs are invoked with fixed argument lists and no shell, and nothing
// is written outside the paths a command names.

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"runtime/debug"
	"sort"
	"strings"

	"crypto/sha256"
	"github.com/SCKelemen/oak/buildcache"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp/server"
	"github.com/SCKelemen/oak/modules"
	"runtime"
)

// command is one top-level oak command.
type command struct {
	name    string
	summary string
	usage   string
	run     func(args []string) int
}

// commands lists the top-level commands in help order.
var commands []command

func init() {
	commands = []command{
		{"build", "compile a package to an executable (or C with -o x.c / -emit-c)", "oak build [-o out] [-emit-c] [-header out.h] [-lean out.lean] [-metal out.metal] [-profile default|strict] [-lines] [dir|file.oak]", buildPackage},
		{"run", "compile and run a package", "oak run [-profile default|strict] [dir]", runPackage},
		{"install", "compile a package and install the executable into $OAKBIN", "oak install [-profile default|strict] [dir]", installPackage},
		{"vet", "check a package without generating code and list what the checker recorded", "oak vet [-profile default|strict] [dir|file.oak]", vetPackage},
		{"test", "run the tests of a package", "oak test [flags] [dir]", nil},
		{"list", "list the packages of the module with their imports", "oak list [-json] [-deps] [dir]", listPackages},
		{"doc", "print the public declarations of a module or package", "oak doc [-package P] [dir] [name]", docCommand},
		{"fmt", "canonicalize whitespace in Oak source (meaning-preserving)", "oak fmt [-l] [-w] [file.oak|dir]...", fmtCommand},
		{"mod", "module maintenance: init, download, tidy, edit, graph, why, vendor, verify, api, diff, bump, compat, pack, upgrade, try", "oak mod <subcommand> [args]", modCommand},
		{"clean", "remove the build cache or the module cache", "oak clean [-cache] [-modcache]", cleanCommand},
		{"env", "print oak environment information", "oak env [NAME...]", envCommand},
		{"repl", "start the interactive session", "oak repl", nil},
		{"lsp", "run the language server over stdio (editors start this)", "oak lsp", lspCommand},
		{"protocol", "protocol tooling", "oak protocol [args]", nil},
		{"prove", "discharge the package's theorems: decided, proved by Lean, refuted, or open", "oak prove [-lean out.lean [-check]] [-cases N] [dir|file.oak]", nil},
		{"version", "print the oak version", "oak version", versionCommand},
		{"completion", "print a shell completion script", "oak completion bash|zsh|fish", completionCommand},
		{"help", "show help for a command", "oak help [command]", helpCommand},
	}
}

func findCommand(name string) *command {
	for i := range commands {
		if commands[i].name == name {
			return &commands[i]
		}
	}
	return nil
}

func printUsage(out io.Writer) {
	fmt.Fprintln(out, "Oak is a tool for managing Oak source code.")
	fmt.Fprintln(out)
	fmt.Fprintln(out, "Usage:")
	fmt.Fprintln(out)
	fmt.Fprintln(out, "\toak <command> [arguments]")
	fmt.Fprintln(out)
	fmt.Fprintln(out, "The commands are:")
	fmt.Fprintln(out)
	for _, c := range commands {
		fmt.Fprintf(out, "\t%-12s%s\n", c.name, c.summary)
	}
	fmt.Fprintln(out)
	fmt.Fprintln(out, "Use \"oak help <command>\" for more information about a command.")
	fmt.Fprintln(out, "Running \"oak\" with no arguments starts the REPL; \"oak file.oak\" compiles one file to C.")
}

func helpCommand(args []string) int {
	if len(args) == 0 {
		printUsage(os.Stdout)
		return 0
	}
	c := findCommand(args[0])
	if c == nil {
		fmt.Fprintf(os.Stderr, "oak help %s: unknown command\n", args[0])
		return 2
	}
	fmt.Printf("usage: %s\n\n%s\n", c.usage, c.summary)
	if c.name == "mod" {
		fmt.Println()
		printModUsage(os.Stdout)
	}
	return 0
}

// versionCommand prints the module version and VCS revision recorded in the
// binary by the Go toolchain.
func versionCommand(args []string) int {
	info, ok := debug.ReadBuildInfo()
	if !ok {
		fmt.Println("oak version unknown")
		return 0
	}
	revision, modified := "", ""
	for _, setting := range info.Settings {
		switch setting.Key {
		case "vcs.revision":
			revision = setting.Value
		case "vcs.modified":
			if setting.Value == "true" {
				modified = " (modified)"
			}
		}
	}
	version := info.Main.Version
	if version == "" || version == "(devel)" {
		version = "devel"
	}
	if revision != "" {
		if len(revision) > 12 {
			revision = revision[:12]
		}
		version += " " + revision + modified
	}
	fmt.Printf("oak version %s %s\n", version, info.GoVersion)
	return 0
}

// envVariables are the environment variables oak reads, with how each
// default is resolved when unset.
var envVariables = []struct {
	name, describe string
	resolve        func() string
}{
	{"OAKMODCACHE", "module cache; unset means dependencies resolve only through replace directives", func() string { return os.Getenv("OAKMODCACHE") }},
	{"OAKBIN", "where oak install puts executables (default $HOME/.oak/bin)", defaultBinDir},
	{"OAKCACHE", "build cache of compiled executables (default: the user cache directory, oak/; off disables)", func() string {
		dir, err := buildcache.Dir()
		if err != nil {
			return "off"
		}
		return dir
	}},
	{"OAK_LEAN_DIR", "spec/lean directory for :lean check (default: found above the working directory)", func() string { return os.Getenv("OAK_LEAN_DIR") }},
	{"OAKROOT", "the module root of the working directory (derived)", moduleRootOf},
}

func envCommand(args []string) int {
	wanted := map[string]bool{}
	for _, name := range args {
		wanted[name] = true
	}
	for _, variable := range envVariables {
		if len(wanted) != 0 && !wanted[variable.name] {
			continue
		}
		value := variable.resolve()
		if len(wanted) != 0 {
			fmt.Println(value)
			continue
		}
		fmt.Printf("%s=%q\n", variable.name, value)
	}
	return 0
}

func defaultBinDir() string {
	if bin := os.Getenv("OAKBIN"); bin != "" {
		return bin
	}
	home, err := os.UserHomeDir()
	if err != nil {
		return ""
	}
	return filepath.Join(home, ".oak", "bin")
}

// moduleRootOf walks up from the working directory to the nearest oak.mod.
func moduleRootOf() string {
	dir, err := os.Getwd()
	if err != nil {
		return ""
	}
	for {
		if info, err := os.Stat(filepath.Join(dir, modules.ManifestFile)); err == nil && !info.IsDir() {
			return dir
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return ""
		}
		dir = parent
	}
}

// vetPackage runs every semantic gate without generating code and prints
// what the checker recorded — errors, and the assumptions it could not
// discharge (unbounded loops, tail cycles, unsafe admissions) — the same
// list the REPL's :obligations shows.
func vetPackage(args []string) int {
	target, profile := ".", ""
	fs := newFlagSet("vet", "oak vet [-profile default|strict] [dir|file.oak|pattern]...")
	fs.StringVar(&profile, "profile", "", "discipline profile: default or strict")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	targets, err := expandPackagePatterns(rest)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak vet: %v\n", err)
		return 1
	}
	if len(targets) > 1 {
		status := 0
		for _, one := range targets {
			if vetOne(one, profile) != 0 {
				status = 1
			}
		}
		return status
	}
	target = targets[0]
	if !validProfile(profile) {
		fmt.Fprintf(os.Stderr, "oak vet: unknown profile %q (default or strict)\n", profile)
		return 2
	}
	return vetOne(target, profile)
}

// vetOne checks one package or file.
func vetOne(target, profile string) int {
	comp, err := compilationFor(target)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak vet: %v\n", err)
		return 1
	}
	model, err := comp.WithProfile(profile).SemanticModel().Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	recorded := 0
	for _, d := range model.Diagnostics {
		if d == nil || d.Severity == diagnostic.SeverityError {
			continue
		}
		recorded++
		fmt.Println(modules.DemangleText(d.PlainText()))
	}
	// Declared operator laws are the author's claims, not the checker's
	// findings (docs/spec/10-syntax.md section 14a): list them beside the
	// assumptions so nothing that licenses a regrouping goes unseen.
	if model.TypeChecker != nil {
		for _, law := range model.TypeChecker.OperatorLaws() {
			fmt.Printf("law: operator(%s) %s on %s declares %s — declared, not checked; the REPL's :lean states it\n", law.Symbol, modules.DemangleText(law.Function), modules.DemangleText(law.Type), law.Law)
		}
	}
	if recorded == 0 {
		fmt.Printf("%s: no recorded assumptions\n", target)
		return 0
	}
	fmt.Printf("%d recorded assumption(s); the strict profile rejects them, the REPL's :lean states them\n", recorded)
	return 0
}

// compilationFor builds a Compilation for a package directory or a single
// source file.
func compilationFor(target string) (compiler.Compilation, error) {
	info, err := os.Stat(target)
	if err != nil {
		return compiler.Compilation{}, err
	}
	if info.IsDir() {
		return compiler.New().WithPackageDir(target), nil
	}
	source, err := os.ReadFile(target)
	if err != nil {
		return compiler.Compilation{}, err
	}
	return compiler.New().WithSource(target, string(source)), nil
}

// listPackages prints the packages of the module at dir (or, with -deps,
// every package the module's build reaches) with their imports.
func listPackages(args []string) int {
	dir, asJSON, deps := ".", false, false
	fs := newFlagSet("list", "oak list [-json] [-deps] [dir|pattern]")
	fs.BoolVar(&asJSON, "json", false, "one JSON object per package")
	fs.BoolVar(&deps, "deps", false, "include every package a build reaches (dependencies, standard library)")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	var only map[string]bool
	if len(rest) > 0 {
		dir = strings.TrimSuffix(strings.TrimSuffix(rest[0], "..."), "/")
		if dir == "" {
			dir = "."
		}
		if isPattern(rest[0]) {
			targets, err := expandPackagePatterns(rest[:1])
			if err != nil {
				fmt.Fprintf(os.Stderr, "oak list: %v\n", err)
				return 1
			}
			only = map[string]bool{}
			for _, target := range targets {
				if abs, err := filepath.Abs(target); err == nil {
					only[abs] = true
				}
			}
			if moduleDir := enclosingModule(mustAbs(dir)); moduleDir != "" {
				dir = moduleDir
			}
		}
	}
	manifest, packages, err := compiler.ModulePackages(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak list: %v\n", err)
		return 1
	}
	type listed struct {
		Path    string   `json:"path"`
		Dir     string   `json:"dir,omitempty"`
		Module  string   `json:"module"`
		Imports []string `json:"imports"`
	}
	seen := map[string]bool{}
	var out []listed
	paths := make([]string, 0, len(packages))
	for path := range packages {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	for _, path := range paths {
		if only != nil {
			if abs, err := filepath.Abs(packages[path]); err != nil || !only[abs] {
				continue
			}
		}
		tree, err := compiler.New().WithPackageDir(packages[path]).Parse().Get()
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak list: %s: %v\n", path, err)
			return 1
		}
		for _, loaded := range tree.Modules.Packages {
			if seen[loaded] {
				continue
			}
			inModule := modules.HasPathPrefix(loaded, manifest.Path)
			if !deps && !inModule {
				continue
			}
			seen[loaded] = true
			entry := listed{Path: loaded, Module: tree.Modules.ModuleOf[loaded], Imports: tree.Modules.Imports[loaded]}
			if inModule {
				entry.Dir = packages[loaded]
			}
			if tree.Modules.StandardLibrary[loaded] {
				entry.Module = "std"
			}
			if entry.Imports == nil {
				entry.Imports = []string{}
			}
			out = append(out, entry)
		}
	}
	sort.Slice(out, func(i, j int) bool { return out[i].Path < out[j].Path })
	if asJSON {
		encoder := json.NewEncoder(os.Stdout)
		encoder.SetIndent("", "  ")
		if err := encoder.Encode(out); err != nil {
			fmt.Fprintf(os.Stderr, "oak list: %v\n", err)
			return 1
		}
		return 0
	}
	for _, entry := range out {
		fmt.Println(entry.Path)
		for _, imported := range entry.Imports {
			fmt.Printf("\t%s\n", imported)
		}
	}
	return 0
}

// cleanCommand removes the module cache. Only -modcache is defined, and only
// an explicit $OAKMODCACHE that is a directory is removed: the tool never
// guesses a location to delete.
func cleanCommand(args []string) int {
	modcache, buildCache := false, false
	fs := newFlagSet("clean", "oak clean [-cache] [-modcache]")
	fs.BoolVar(&modcache, "modcache", false, "empty the module cache named by $OAKMODCACHE")
	fs.BoolVar(&buildCache, "cache", false, "remove the build cache ($OAKCACHE)")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	if (!modcache && !buildCache) || len(rest) != 0 {
		fmt.Fprintln(os.Stderr, "usage: oak clean [-cache] [-modcache]")
		return 2
	}
	if buildCache {
		dir, err := buildcache.Clean()
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak clean: %v\n", err)
			return 1
		}
		fmt.Printf("removed build cache %s\n", dir)
	}
	if !modcache {
		return 0
	}
	cache := os.Getenv("OAKMODCACHE")
	if cache == "" {
		fmt.Fprintln(os.Stderr, "oak clean: OAKMODCACHE is not set; nothing to remove")
		return 1
	}
	info, err := os.Stat(cache)
	if err != nil || !info.IsDir() {
		fmt.Fprintf(os.Stderr, "oak clean: %s is not a directory\n", cache)
		return 1
	}
	entries, err := os.ReadDir(cache)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak clean: %v\n", err)
		return 1
	}
	for _, entry := range entries {
		if err := os.RemoveAll(filepath.Join(cache, entry.Name())); err != nil {
			fmt.Fprintf(os.Stderr, "oak clean: %v\n", err)
			return 1
		}
	}
	fmt.Printf("removed %d entr%s from %s\n", len(entries), plural(len(entries), "y", "ies"), cache)
	return 0
}

func mustAbs(dir string) string {
	abs, err := filepath.Abs(dir)
	if err != nil {
		return dir
	}
	return abs
}

func plural(n int, one, many string) string {
	if n == 1 {
		return one
	}
	return many
}

// compileBinary emits C for the package (and, in native asm mode, the asm
// units' companion object) and compiles it with the system C compiler into
// binary (fixed argument list, no shell).
func compileBinary(comp compiler.Compilation, binary, asmMode string) error {
	code, object, err := emitForHost(comp, asmMode)
	if err != nil {
		return err
	}
	inputs, err := comp.LinkInputs()
	if err != nil {
		return err
	}
	_, err = compileC(code, object, inputs, binary)
	return err
}

// ccFlags are the fixed C compiler flags for executables: -ffp-contract=off
// keeps floating-point semantics exactly as written (docs/spec/90-backend.md
// section 7a); -lm links the C99 math library the float intrinsics lower to.
var ccFlags = []string{"-std=c99", "-O1", "-ffp-contract=off"}

// compileC turns emitted C (and an optional asm companion object) into the
// executable at binary, through the build cache: a hit copies the cached
// binary, a miss compiles with a fixed argument list and stores the result.
// The manifests' native inputs (`link`, `framework`; docs/spec/83-modules.md
// section 4.6) follow the program on the command line, objects by path and
// frameworks as `-framework Name` on macOS; their contents are part of the
// cache identity, so a rebuilt library invalidates the cached executable.
// It reports whether the binary came from the cache.
func compileC(code string, object []byte, inputs []compiler.LinkInput, binary string) (bool, error) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		return false, errors.New("no C compiler (cc) on PATH; use -emit-c to write C instead")
	}
	linkArgs, linkIdentity, err := linkArguments(inputs, os.Stderr)
	if err != nil {
		return false, err
	}
	key := ""
	if identity, err := buildcache.CompilerIdentity(cc); err == nil {
		key = buildcache.Key("oak-exe-v1", code, string(object), identity, strings.Join(ccFlags, " "), linkIdentity)
		if cached, ok := buildcache.Lookup(key); ok {
			if err := buildcache.Copy(cached, binary); err == nil {
				return true, nil
			}
		}
	}
	work, err := os.MkdirTemp("", "oak-build-")
	if err != nil {
		return false, err
	}
	defer os.RemoveAll(work)
	cPath := filepath.Join(work, "program.c")
	if err := os.WriteFile(cPath, []byte(code), 0o600); err != nil {
		return false, err
	}
	ccArgs := append(append([]string{}, ccFlags...), "-o", binary, cPath)
	if object != nil {
		objPath := filepath.Join(work, "asm.o")
		if err := os.WriteFile(objPath, object, 0o600); err != nil {
			return false, err
		}
		ccArgs = append(ccArgs, objPath)
	}
	ccArgs = append(ccArgs, linkArgs...)
	build := exec.Command(cc, append(ccArgs, "-lm")...)
	build.Stdout, build.Stderr = os.Stdout, os.Stderr
	if err := build.Run(); err != nil {
		return false, fmt.Errorf("C compilation failed: %v", err)
	}
	if key != "" {
		// A failed store is a miss next time, never a failed build.
		_ = buildcache.Store(key, binary)
	}
	return false, nil
}

// linkArguments spells the manifests' native inputs as C compiler arguments
// (argv, never a shell) and returns an identity string covering each
// object's bytes and each framework's name, for build-cache keys. On hosts
// without frameworks a `framework` line is skipped with one note on notes.
func linkArguments(inputs []compiler.LinkInput, notes io.Writer) ([]string, string, error) {
	var args []string
	var identity strings.Builder
	noted := false
	for _, input := range inputs {
		switch input.Kind {
		case "object":
			data, err := os.ReadFile(input.Path)
			if err != nil {
				return nil, "", fmt.Errorf("link %s: %v", input.Path, err)
			}
			sum := sha256.Sum256(data)
			fmt.Fprintf(&identity, "object %s %x\n", input.Path, sum)
			args = append(args, input.Path)
		case "framework":
			fmt.Fprintf(&identity, "framework %s\n", input.Path)
			if runtime.GOOS == "darwin" {
				args = append(args, "-framework", input.Path)
			} else if !noted && notes != nil {
				fmt.Fprintf(notes, "note: framework directives apply on macOS only; %s not linked on %s\n", input.Path, runtime.GOOS)
				noted = true
			}
		}
	}
	return args, identity.String(), nil
}

// lspCommand runs the language server on stdin/stdout
// (docs/spec/115-tooling.md section 4).
func lspCommand(args []string) int {
	fs := newFlagSet("lsp", "oak lsp")
	if _, code, stop := parseFlags(fs, args); stop {
		return code
	}
	if err := server.ServeStdio(); err != nil {
		fmt.Fprintf(os.Stderr, "oak lsp: %v\n", err)
		return 1
	}
	return 0
}

// executableName names a package's executable: the last segment of the root
// package's import path, or of the module path when the root is the
// clause-less `main`, or of the directory outside any module. The name must
// be a valid package name.
func executableName(dir string) (string, error) {
	name := ""
	if tree, err := compiler.New().WithPackageDir(dir).Parse().Get(); err == nil && tree.Modules != nil {
		name = modules.LastSegment(tree.Modules.RootPackage)
		if (name == "main" || name == "") && tree.Modules.RootModule != "" {
			name = modules.LastSegment(tree.Modules.RootModule)
		}
	}
	if name == "" || name == "main" {
		abs, err := filepath.Abs(dir)
		if err != nil {
			return "", err
		}
		name = filepath.Base(abs)
	}
	if !modules.ValidPackageName(name) {
		return "", fmt.Errorf("%q is not a package name; build with -o instead", name)
	}
	return name, nil
}

// installPackage builds the package's executable into $OAKBIN (default
// $HOME/.oak/bin), named after the package (executableName).
func installPackage(args []string) int {
	dir, profile := ".", ""
	fs := newFlagSet("install", "oak install [-profile default|strict] [dir]")
	fs.StringVar(&profile, "profile", "", "discipline profile: default or strict")
	rest, code, stop := parseFlags(fs, args)
	if stop {
		return code
	}
	if len(rest) > 0 {
		dir = rest[0]
	}
	if !validProfile(profile) {
		fmt.Fprintf(os.Stderr, "oak install: unknown profile %q (default or strict)\n", profile)
		return 2
	}
	bin := defaultBinDir()
	if bin == "" {
		fmt.Fprintln(os.Stderr, "oak install: cannot determine $OAKBIN or the home directory")
		return 1
	}
	if err := os.MkdirAll(bin, 0o755); err != nil {
		fmt.Fprintf(os.Stderr, "oak install: %v\n", err)
		return 1
	}
	name, err := executableName(dir)
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak install: %v\n", err)
		return 1
	}
	target := filepath.Join(bin, name)
	comp := compiler.New().WithPackageDir(dir).WithProfile(profile).WithDiagnosticSink(reportAsmVerdict)
	if err := compileBinary(comp, target, defaultAsmMode()); err != nil {
		fmt.Fprintf(os.Stderr, "oak install: %v\n", err)
		return 1
	}
	fmt.Printf("installed %s\n", target)
	return 0
}
