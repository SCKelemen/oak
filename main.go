package main

import (
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"os/user"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/repl"
	"github.com/SCKelemen/oak/testrunner"
)

func main() {
	if len(os.Args) > 1 && os.Args[1] == "test" {
		os.Exit(testrunner.Main(os.Args[2:], os.Stdout, os.Stderr))
	}
	if len(os.Args) > 1 && os.Args[1] == "build" {
		os.Exit(buildPackage(os.Args[2:]))
	}
	if len(os.Args) > 1 && os.Args[1] == "mod" {
		os.Exit(modCommand(os.Args[2:]))
	}
	if len(os.Args) > 1 && os.Args[1] == "run" {
		os.Exit(runPackage(os.Args[2:]))
	}

	if len(os.Args) > 1 {
		// Compile mode: oak file.oak
		filename := os.Args[1]
		if !strings.HasSuffix(filename, ".oak") {
			fmt.Printf("Error: expected .oak file, got %s\n", filename)
			os.Exit(1)
		}

		source, err := os.ReadFile(filename)
		if err != nil {
			fmt.Printf("Error reading file: %v\n", err)
			os.Exit(1)
		}

		output, err := compiler.New().
			WithSource(filename, string(source)).
			EmitC().
			Get()
		if err != nil {
			fmt.Printf("Compilation error: %v\n", err)
			os.Exit(1)
		}

		baseName := strings.TrimSuffix(filename, ".oak")
		outputFile := baseName + ".c"
		if err := os.WriteFile(outputFile, []byte(output), 0644); err != nil {
			fmt.Printf("Error writing output file: %v\n", err)
			os.Exit(1)
		}

		fmt.Printf("Compiled %s -> %s\n", filename, outputFile)
		return
	}

	// REPL mode
	usr, err := user.Current()
	if err != nil {
		panic(err)
	}

	fmt.Printf("Hello %s, welcome to Oak 🌳\n", usr.Username)
	fmt.Printf("Type Oak code or 'exit' to quit\n")
	repl.Start(os.Stdin, os.Stdout)
}

// buildPackage implements `oak build [-o out.c] [dir]`: the package at dir
// (default ".") and everything it imports, resolved through the enclosing
// module's oak.mod (docs/spec/83-modules.md), compile to one C translation
// unit written to out.c (default <dir-name>.c in the current directory).
func buildPackage(args []string) int {
	dir := "."
	output := ""
	profile := ""
	for i := 0; i < len(args); i++ {
		switch {
		case args[i] == "-o" && i+1 < len(args):
			output = args[i+1]
			i++
		case args[i] == "-profile" && i+1 < len(args):
			profile = args[i+1]
			i++
		case strings.HasPrefix(args[i], "-"):
			fmt.Fprintf(os.Stderr, "oak build: unknown flag %s\nusage: oak build [-o out.c] [-profile default|strict] [dir]\n", args[i])
			return 2
		default:
			dir = args[i]
		}
	}
	if !validProfile(profile) {
		fmt.Fprintf(os.Stderr, "oak build: unknown profile %q (default or strict; docs/spec/85-discipline.md section 1)\n", profile)
		return 2
	}
	code, err := compiler.New().WithPackageDir(dir).WithProfile(profile).EmitC().Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	if output == "" {
		abs, err := filepath.Abs(dir)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
			return 1
		}
		output = filepath.Base(abs) + ".c"
	}
	if err := os.WriteFile(output, []byte(code), 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
		return 1
	}
	fmt.Printf("Built %s -> %s\n", dir, output)
	return 0
}

// modCommand implements `oak mod download [dir]`: fetch every requirement of
// the module's oak.mod that pins an archive location and digest into the
// module cache ($OAKMODCACHE), verifying the digest before extraction
// (docs/spec/83-modules.md section 4.4). The compiler itself never fetches.
func modCommand(args []string) int {
	if len(args) == 0 || args[0] != "download" {
		fmt.Fprintln(os.Stderr, "usage: oak mod download [dir]")
		return 2
	}
	dir := "."
	if len(args) > 1 {
		dir = args[1]
	}
	text, err := os.ReadFile(filepath.Join(dir, modules.ManifestFile))
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	manifest, err := modules.ParseManifest(string(text))
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	fetcher := &modules.Fetcher{
		Cache: os.Getenv("OAKMODCACHE"),
		Log:   func(format string, args ...interface{}) { fmt.Printf(format+"\n", args...) },
	}
	if err := fetcher.Download(context.Background(), manifest); err != nil {
		fmt.Fprintf(os.Stderr, "oak mod: %v\n", err)
		return 1
	}
	return 0
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
	for i := 0; i < len(args); i++ {
		switch {
		case args[i] == "-profile" && i+1 < len(args):
			profile = args[i+1]
			i++
		case strings.HasPrefix(args[i], "-"):
			fmt.Fprintf(os.Stderr, "oak run: unknown flag %s\nusage: oak run [-profile default|strict] [dir]\n", args[i])
			return 2
		default:
			dir = args[i]
		}
	}
	if !validProfile(profile) {
		fmt.Fprintf(os.Stderr, "oak run: unknown profile %q (default or strict; docs/spec/85-discipline.md section 1)\n", profile)
		return 2
	}
	code, err := compiler.New().WithPackageDir(dir).WithProfile(profile).EmitC().Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		fmt.Fprintln(os.Stderr, "oak run: no C compiler (cc) on PATH")
		return 1
	}
	work, err := os.MkdirTemp("", "oak-run-")
	if err != nil {
		fmt.Fprintf(os.Stderr, "oak run: %v\n", err)
		return 1
	}
	defer os.RemoveAll(work)
	cPath := filepath.Join(work, "program.c")
	binary := filepath.Join(work, "program")
	if err := os.WriteFile(cPath, []byte(code), 0o600); err != nil {
		fmt.Fprintf(os.Stderr, "oak run: %v\n", err)
		return 1
	}
	build := exec.Command(cc, "-std=c99", "-O1", "-o", binary, cPath)
	build.Stdout, build.Stderr = os.Stdout, os.Stderr
	if err := build.Run(); err != nil {
		fmt.Fprintf(os.Stderr, "oak run: C compilation failed: %v\n", err)
		return 1
	}
	program := exec.Command(binary)
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
