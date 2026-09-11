package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

// proveCommand implements `oak prove [-lean out.lean] [-cases N] [dir|file.oak]`
// (docs/spec/125-verification.md section 4): type-check the package, run
// the discharge ladder over its theorems, print one line per theorem, and
// with -lean write the Lean projection of the theorems and what they call.
// The exit status is 0 when every theorem is decided, 1 when one is
// refuted or open, 2 on usage or compilation errors.
func proveCommand(args []string, stdout, stderr io.Writer) int {
	flags := flag.NewFlagSet("oak prove", flag.ContinueOnError)
	flags.SetOutput(stderr)
	leanOut := flags.String("lean", "", "write the Lean projection of the theorems here")
	cases := flags.Int("cases", prove.DefaultCases, "largest parameter domain the exhaustive decider enumerates")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if flags.NArg() > 1 {
		fmt.Fprintln(stderr, "usage: oak prove [-lean out.lean] [-cases N] [dir|file.oak]")
		return 2
	}
	target := "."
	if flags.NArg() == 1 {
		target = flags.Arg(0)
	}
	target = filepath.Clean(target)
	comp := compiler.New()
	if info, err := os.Stat(target); err == nil && info.IsDir() {
		comp = comp.WithPackageDir(target)
	} else {
		source, err := os.ReadFile(target)
		if err != nil {
			fmt.Fprintf(stderr, "oak prove: %v\n", err)
			return 2
		}
		comp = comp.WithSource(target, string(source))
	}
	model, err := comp.Check().Get()
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	results, err := prove.Theorems(model, *cases)
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	if len(results) == 0 {
		fmt.Fprintln(stdout, "oak prove: no theorems")
		return 0
	}
	exit := 0
	for _, r := range results {
		fmt.Fprintf(stdout, "%-9s %s: %s\n", r.Status, r.Name, r.Detail)
		if r.Status != prove.Decided {
			exit = 1
		}
	}
	fmt.Fprintf(stdout, "oak prove: %s\n", prove.Summary(results))
	if *leanOut != "" {
		text, err := comp.EmitLeanRoots("Oak.Theorems", prove.Names(model)).Get()
		if err != nil {
			fmt.Fprintf(stderr, "oak prove: lean: %v\n", err)
			return 2
		}
		if err := os.WriteFile(*leanOut, []byte(text), 0o644); err != nil {
			fmt.Fprintf(stderr, "oak prove: %v\n", err)
			return 2
		}
		fmt.Fprintf(stdout, "oak prove: wrote %s\n", *leanOut)
	}
	return exit
}
