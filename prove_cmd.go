package main

import (
	"flag"
	"fmt"
	oaktarget "github.com/SCKelemen/oak/target"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/asm"
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
	check := flags.Bool("check", false, "run Lean on the projection (-lean) and report the statements it proves")
	leanBinary := flags.String("lean-binary", "lean", "the Lean executable -check runs")
	cases := flags.Int("cases", prove.DefaultCases, "largest parameter domain the exhaustive decider enumerates")
	solver := flags.String("solver", "oak", "the bit-level decider: oak (the solver written in Oak, prove/solver) or go")
	cross := flags.String("cross", "go", "with -solver oak, the cross-check of every bit-level verdict: go (the Go decider under the same order must agree, node for node) or none")
	witness := flags.Bool("witness", false, "also evaluate the exhaustively decided theorems in the compiled program")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if flags.NArg() > 1 || (*check && *leanOut == "") {
		fmt.Fprintln(stderr, "usage: oak prove [-lean out.lean [-check [-lean-binary lean]]] [-cases N] [-witness] [-solver oak|go] [-cross go|none] [dir|file.oak]")
		return 2
	}
	target := "."
	if flags.NArg() == 1 {
		target = flags.Arg(0)
	}
	target = filepath.Clean(target)
	// Invariant candidates get their base and step obligations generated
	// before checking (prove/protocols.go), and declared operator laws
	// their theorems (prove/laws.go).
	comp := compiler.New().WithSyntaxRewrite(prove.Obligations)
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
	results, err := prove.TheoremsWith(model, *cases, *solver == "oak")
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	if len(results) == 0 {
		fmt.Fprintln(stdout, "oak prove: no theorems")
		return 0
	}
	if *solver == "oak" {
		// The Oak solver (prove/solver/bdd.oak) decides the bit-level rung:
		// every pending theorem's variants race in one generated program,
		// and with -check go the Go decider replays the winning order and
		// must reach the same verdict with the same number of nodes.
		var names []string
		var theorems [][]asm.Problem
		for _, r := range results {
			if r.Status == prove.Pending {
				names = append(names, r.Name)
				theorems = append(theorems, r.Problems)
			}
		}
		verdicts, err := runOakSolver(theorems, asm.NodeBudget)
		if err != nil {
			fmt.Fprintf(stderr, "oak prove: %v\n", err)
			return 2
		}
		byName := map[string]prove.SolverVerdict{}
		for i, name := range names {
			byName[name] = verdicts[i]
		}
		results = prove.ResolvePending(results, byName, func(name string) (prove.Result, bool) { return prove.GoDecision(model, name, "") })
		if *cross == "go" {
			for i, r := range results {
				if _, oak := byName[r.Name]; !oak || !strings.Contains(r.Detail, "the Oak solver") || (r.Status != prove.Decided && r.Status != prove.Refuted) {
					continue
				}
				fromGo, ok := prove.GoDecision(model, r.Name, r.Order)
				switch {
				case !ok:
					continue
				case r.Status == prove.Decided && fromGo.Status == prove.Decided && fromGo.Nodes == r.Nodes:
					results[i].Detail += "; the Go decider agrees"
				case r.Status == prove.Refuted && fromGo.Status == prove.Refuted:
					results[i].Detail += "; the Go decider agrees"
				default:
					results[i].Status = prove.Open
					results[i].Detail = fmt.Sprintf("the Go decider disagrees with the Oak solver: Go %s (%s), Oak %s (%s)", fromGo.Status, fromGo.Detail, r.Status, r.Detail)
				}
			}
		}
	}
	if *leanOut != "" {
		// A theorem the extractor cannot state (a recursive callee, a
		// construct outside the subset) stays open with the extractor's
		// reason; the projection carries the rest.
		var roots []string
		for i, r := range results {
			if _, err := comp.EmitLeanRoots("Oak.Theorems", []string{r.Name}).Get(); err != nil {
				if r.Status == prove.Open {
					results[i].Detail += " (not projected: " + err.Error() + ")"
				}
				continue
			}
			roots = append(roots, r.Name)
		}
		text, err := comp.EmitLeanRoots("Oak.Theorems", roots).Get()
		if err != nil {
			fmt.Fprintf(stderr, "oak prove: lean: %v\n", err)
			return 2
		}
		if err := os.WriteFile(*leanOut, []byte(text), 0o644); err != nil {
			fmt.Fprintf(stderr, "oak prove: %v\n", err)
			return 2
		}
		if *check {
			checked, err := prove.CheckWithLean(*leanBinary, *leanOut, text, results)
			if err != nil {
				fmt.Fprintf(stderr, "oak prove: %v\n", err)
				return 2
			}
			results = checked
		}
	}
	if *witness {
		// The compiled witness (prove/witness.go): the same theorems, run
		// through the backend on the host.
		var plan prove.WitnessPlan
		binary := filepath.Join(os.TempDir(), fmt.Sprintf("oak-witness-%d", os.Getpid()))
		defer os.Remove(binary)
		witnessed := comp.WithSyntaxRewrite(prove.WitnessRewriteWithin(results, *cases, &plan))
		host := oaktarget.Host()
		if err := compileBinary(witnessed, binary, defaultAsmMode(host), host, ""); err != nil {
			fmt.Fprintf(stderr, "oak prove: witness: %v\n", err)
			return 2
		}
		run := exec.Command(binary)
		run.Stdout, run.Stderr = stdout, stderr
		status := 0
		if err := run.Run(); err != nil {
			exitErr, isExit := err.(*exec.ExitError)
			if !isExit {
				fmt.Fprintf(stderr, "oak prove: witness: %v\n", err)
				return 2
			}
			status = exitErr.ExitCode()
		}
		results = prove.ApplyWitness(results, plan, status)
		if skips := prove.WitnessSkips(plan); skips != "" {
			fmt.Fprintf(stdout, "oak prove: witness left to the interpreter: %s\n", skips)
		}
	}
	exit := 0
	for _, r := range results {
		fmt.Fprintf(stdout, "%-9s %s: %s\n", r.Status, r.Name, r.Detail)
		if r.Status != prove.Decided && r.Status != prove.Proved {
			exit = 1
		}
	}
	fmt.Fprintf(stdout, "oak prove: %s\n", prove.Summary(results))
	if *leanOut != "" {
		fmt.Fprintf(stdout, "oak prove: wrote %s\n", *leanOut)
	}
	return exit
}
