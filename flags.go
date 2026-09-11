package main

// Uniform flag handling and package patterns for the oak command
// (docs/spec/115-tooling.md section 1): every command parses its flags with
// the standard flag package, so `oak <command> -h` prints usage, unknown
// flags are usage errors (exit 2), and flags precede positional arguments.
// `./...` and `dir/...` expand to the packages under a directory.

import (
	"errors"
	"flag"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/modules"
)

// newFlagSet returns a flag set for the command whose -h prints usage and
// the flag defaults to stdout.
func newFlagSet(name, usage string) *flag.FlagSet {
	fs := flag.NewFlagSet(name, flag.ContinueOnError)
	fs.SetOutput(os.Stderr)
	fs.Usage = func() {
		fmt.Fprintf(os.Stdout, "usage: %s\n", usage)
		if hasFlags(fs) {
			fmt.Fprintln(os.Stdout)
			fmt.Fprintln(os.Stdout, "flags:")
			fs.SetOutput(os.Stdout)
			fs.PrintDefaults()
			fs.SetOutput(os.Stderr)
		}
	}
	return fs
}

func hasFlags(fs *flag.FlagSet) bool {
	any := false
	fs.VisitAll(func(*flag.Flag) { any = true })
	return any
}

// parseFlags parses args. It returns the positional arguments, or an exit
// code and stop=true when parsing ended the command: 0 after -h, 2 on a
// usage error (already reported).
func parseFlags(fs *flag.FlagSet, args []string) (rest []string, code int, stop bool) {
	if err := fs.Parse(args); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return nil, 0, true
		}
		fmt.Fprintf(os.Stderr, "run 'oak %s -h' for usage\n", fs.Name())
		return nil, 2, true
	}
	return fs.Args(), 0, false
}

// splitProgramArgs separates `oak run` style arguments at the first `--`:
// what precedes belongs to oak, what follows to the program.
func splitProgramArgs(args []string) (own, program []string) {
	for i, arg := range args {
		if arg == "--" {
			return args[:i], args[i+1:]
		}
	}
	return args, nil
}

// isPattern reports whether an argument is a package pattern (`./...`,
// `dir/...`).
func isPattern(arg string) bool {
	return arg == "..." || strings.HasSuffix(arg, "/...")
}

// expandPackagePatterns turns arguments into package directories: a plain
// argument stands for itself; `dir/...` expands to every package directory
// under dir — the module's packages when an oak.mod is above dir, otherwise
// every directory under dir holding .oak files (hidden, vendor, and testdata
// directories excluded). An empty list means ".".
func expandPackagePatterns(args []string) ([]string, error) {
	if len(args) == 0 {
		return []string{"."}, nil
	}
	var out []string
	seen := map[string]bool{}
	add := func(dir string) {
		clean := filepath.Clean(dir)
		if !seen[clean] {
			seen[clean] = true
			out = append(out, clean)
		}
	}
	for _, arg := range args {
		if !isPattern(arg) {
			add(arg)
			continue
		}
		root := strings.TrimSuffix(arg, "...")
		root = strings.TrimSuffix(root, "/")
		if root == "" || root == "." {
			root = "."
		}
		dirs, err := packagesUnder(root)
		if err != nil {
			return nil, err
		}
		if len(dirs) == 0 {
			return nil, fmt.Errorf("%s: no packages under %s", arg, root)
		}
		for _, dir := range dirs {
			add(dir)
		}
	}
	return out, nil
}

// packagesUnder lists package directories below root, in sorted order.
func packagesUnder(root string) ([]string, error) {
	abs, err := filepath.Abs(root)
	if err != nil {
		return nil, err
	}
	if moduleDir := enclosingModule(abs); moduleDir != "" {
		_, packages, err := compiler.ModulePackages(moduleDir)
		if err != nil {
			return nil, err
		}
		var dirs []string
		for _, dir := range packages {
			if dir == abs || strings.HasPrefix(dir, abs+string(filepath.Separator)) {
				dirs = append(dirs, relativeOrAbs(dir))
			}
		}
		sort.Strings(dirs)
		return dirs, nil
	}
	var dirs []string
	err = filepath.WalkDir(abs, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() {
			name := entry.Name()
			if path != abs && (strings.HasPrefix(name, ".") || name == modules.VendorDir || name == "testdata") {
				return filepath.SkipDir
			}
			return nil
		}
		if strings.HasSuffix(entry.Name(), ".oak") && !strings.HasSuffix(entry.Name(), "_test.oak") {
			dir := filepath.Dir(path)
			if len(dirs) == 0 || dirs[len(dirs)-1] != dir {
				dirs = append(dirs, dir)
			}
		}
		return nil
	})
	if err != nil {
		return nil, err
	}
	for i, dir := range dirs {
		dirs[i] = relativeOrAbs(dir)
	}
	sort.Strings(dirs)
	return dirs, nil
}

// enclosingModule walks up from dir to the nearest oak.mod, or "".
func enclosingModule(dir string) string {
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

// relativeOrAbs renders a directory relative to the working directory when
// that is shorter and does not leave it.
func relativeOrAbs(dir string) string {
	wd, err := os.Getwd()
	if err != nil {
		return dir
	}
	rel, err := filepath.Rel(wd, dir)
	if err != nil || strings.HasPrefix(rel, "..") {
		return dir
	}
	if rel == "." {
		return "."
	}
	return "./" + rel
}

// completionCommand prints a shell completion script built from the command
// tables; nothing from the invocation is interpolated into it.
func completionCommand(args []string) int {
	if len(args) != 1 {
		fmt.Fprintln(os.Stderr, "usage: oak completion bash|zsh|fish")
		return 2
	}
	names := make([]string, 0, len(commands))
	for _, c := range commands {
		names = append(names, c.name)
	}
	names = append(names, "completion")
	subcommands := []string{"init", "download", "tidy", "edit", "graph", "why", "vendor", "verify", "api", "diff", "bump", "compat", "pack", "upgrade", "try"}
	switch args[0] {
	case "bash":
		fmt.Printf(`# oak bash completion: source this file, or install it under bash_completion.d
_oak() {
  local cur prev
  COMPREPLY=()
  cur="${COMP_WORDS[COMP_CWORD]}"
  prev="${COMP_WORDS[COMP_CWORD-1]}"
  if [ "$COMP_CWORD" -eq 1 ]; then
    COMPREPLY=( $(compgen -W "%s" -- "$cur") )
    return 0
  fi
  if [ "${COMP_WORDS[1]}" = "mod" ] && [ "$COMP_CWORD" -eq 2 ]; then
    COMPREPLY=( $(compgen -W "%s" -- "$cur") )
    return 0
  fi
  if [ "${COMP_WORDS[1]}" = "help" ] && [ "$COMP_CWORD" -eq 2 ]; then
    COMPREPLY=( $(compgen -W "%s" -- "$cur") )
    return 0
  fi
  COMPREPLY=( $(compgen -f -- "$cur") )
}
complete -F _oak oak
`, strings.Join(names, " "), strings.Join(subcommands, " "), strings.Join(names, " "))
	case "zsh":
		fmt.Printf(`#compdef oak
# oak zsh completion: place this file as _oak in a directory on $fpath
_oak() {
  local -a cmds subs
  cmds=(%s)
  subs=(%s)
  if (( CURRENT == 2 )); then
    _describe 'command' cmds
  elif [[ ${words[2]} == mod && CURRENT == 3 ]]; then
    _describe 'mod subcommand' subs
  elif [[ ${words[2]} == help && CURRENT == 3 ]]; then
    _describe 'command' cmds
  else
    _files
  fi
}
_oak "$@"
`, strings.Join(names, " "), strings.Join(subcommands, " "))
	case "fish":
		var b strings.Builder
		b.WriteString("# oak fish completion: save as ~/.config/fish/completions/oak.fish\n")
		for _, c := range commands {
			fmt.Fprintf(&b, "complete -c oak -n '__fish_use_subcommand' -a %s -d '%s'\n", c.name, strings.ReplaceAll(c.summary, "'", ""))
		}
		fmt.Fprintf(&b, "complete -c oak -n '__fish_use_subcommand' -a completion -d 'print a shell completion script'\n")
		for _, sub := range subcommands {
			fmt.Fprintf(&b, "complete -c oak -n '__fish_seen_subcommand_from mod' -a %s\n", sub)
		}
		fmt.Print(b.String())
	default:
		fmt.Fprintf(os.Stderr, "oak completion: unknown shell %q (bash, zsh, fish)\n", args[0])
		return 2
	}
	return 0
}
