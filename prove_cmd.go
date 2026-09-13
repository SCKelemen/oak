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
	solver := flags.String("solver", "oak", "the decider: oak (the Go ladder with the solver written in Oak, prove/solver), self (the prover written in Oak end to end: the file to the rows), or go")
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
	if *solver == "self" {
		// The prover written in Oak (prove/solver/shell.oak): the file to
		// the rows, with the Go ladder as the cross-check when asked.
		return selfProve(target, *cases, *cross == "go", stdout, stderr)
	}
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
		var theorems []oakTheorem
		for _, r := range results {
			if r.Status == prove.Pending {
				names = append(names, r.Name)
				theorems = append(theorems, oakTheorem{Name: r.Name, Problems: r.Problems})
			}
		}
		// The source files go to the parser written in Oak, which finds
		// each pending theorem by name.
		verdicts, err := runOakSolver(theorems, lawSources(target), *cases, asm.NodeBudget)
		if err != nil {
			fmt.Fprintf(stderr, "oak prove: %v\n", err)
			return 2
		}
		byName := map[string]prove.SolverVerdict{}
		for i, name := range names {
			byName[name] = verdicts[i]
		}
		results = prove.ResolvePending(results, byName, func(name string) (prove.Result, bool) { return prove.GoDecision(model, name, "") }, func(name string) (prove.Result, bool) { return prove.GoWitness(model, name) })
		if *cross == "go" {
			for i, r := range results {
				if _, oak := byName[r.Name]; !oak || !(strings.Contains(r.Detail, "the Oak solver") || strings.Contains(r.Detail, "decided in Oak") || strings.Contains(r.Detail, "enumerated in Oak")) || (r.Status != prove.Decided && r.Status != prove.Refuted) {
					continue
				}
				loweredInOak := strings.Contains(r.Detail, "lowered and decided in Oak")
				if strings.Contains(r.Detail, "enumerated in Oak") {
					// The exhaustive rung ran in Oak: the Go interpreter's
					// enumeration must agree.
					fromGo, ok := prove.GoEnumeration(model, r.Name, *cases)
					switch {
					case !ok:
					case r.Status == fromGo.Status:
						results[i].Detail += "; the Go interpreter agrees"
					default:
						results[i].Status = prove.Open
						results[i].Detail = fmt.Sprintf("the Go interpreter disagrees with the Oak enumeration: Go %s (%s), Oak %s (%s)", fromGo.Status, fromGo.Detail, r.Status, r.Detail)
					}
					continue
				}
				replayOrder := r.Order
				if loweredInOak {
					replayOrder = "" // the Oak lowering's orders are its own; any order of the Go decider's may confirm the verdict
				}
				fromGo, ok := prove.GoDecision(model, r.Name, replayOrder)
				if ok && fromGo.Status == prove.Open {
					// The Go lowering does not take the theorem: the Go
					// interpreter's enumeration is the cross-check when the
					// domain is finite, else the verdict stands alone.
					if enumerated, finite := prove.GoEnumeration(model, r.Name, *cases); finite {
						if enumerated.Status == r.Status {
							results[i].Detail += "; the Go interpreter agrees"
						} else {
							results[i].Status = prove.Open
							results[i].Detail = fmt.Sprintf("the Go interpreter disagrees with the Oak solver: Go %s (%s), Oak %s (%s)", enumerated.Status, enumerated.Detail, r.Status, r.Detail)
						}
					} else {
						results[i].Detail += "; the Go decider does not take it"
					}
					continue
				}
				switch {
				case !ok:
					continue
				case loweredInOak && r.Status == fromGo.Status:
					// The Oak lowering's terms are its own; the verdict is what
					// the Go lowering and decider must agree on.
					results[i].Detail += fmt.Sprintf("; the Go lowering and decider agree (%d nodes)", fromGo.Nodes)
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
		// One extraction over every theorem is the common case; only when
		// it fails is each theorem tried alone, to name the ones the
		// extractor cannot state.
		var roots []string
		for _, r := range results {
			roots = append(roots, r.Name)
		}
		text, err := comp.EmitLeanRoots("Oak.Theorems", roots).Get()
		if err != nil {
			roots = roots[:0]
			for i, r := range results {
				if _, probe := comp.EmitLeanRoots("Oak.Theorems", []string{r.Name}).Get(); probe != nil {
					if r.Status == prove.Open {
						results[i].Detail += " (not projected: " + probe.Error() + ")"
					}
					continue
				}
				roots = append(roots, r.Name)
			}
			text, err = comp.EmitLeanRoots("Oak.Theorems", roots).Get()
		}
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

// lawSources reads the Oak sources the prover streams to the parser
// written in Oak: the file itself, or every `.oak` file of the package
// directory, in name order.
func lawSources(target string) [][]byte {
	info, err := os.Stat(target)
	if err != nil {
		return nil
	}
	if !info.IsDir() {
		text, err := os.ReadFile(target)
		if err != nil {
			return nil
		}
		return [][]byte{text}
	}
	entries, err := os.ReadDir(target)
	if err != nil {
		return nil
	}
	var sources [][]byte
	for _, entry := range entries {
		name := entry.Name()
		if entry.IsDir() || !strings.HasSuffix(name, ".oak") || strings.HasPrefix(name, ".") {
			continue
		}
		if text, err := os.ReadFile(filepath.Join(target, name)); err == nil {
			sources = append(sources, text)
		}
	}
	return sources
}

// selfProve runs the prover written in Oak on one law file: the solver
// program in its shell mode (OAK_SOLVER_MODE=prove) reads the file, decides
// every theorem, and prints the rows. With crossCheck the Go ladder decides
// the same file and every row's status must agree.
func selfProve(target string, cases int, crossCheck bool, stdout, stderr io.Writer) int {
	info, err := os.Stat(target)
	if err != nil || info.IsDir() {
		fmt.Fprintf(stderr, "oak prove: -solver self takes one law file, got %s\n", target)
		return 2
	}
	binary, err := oakSolverBinary()
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	absolute, err := filepath.Abs(target)
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	run := exec.Command(binary)
	run.Env = append(os.Environ(), "OAK_SOLVER_MODE=prove", "OAK_PROVE_FILE="+absolute, fmt.Sprintf("OAK_PROVE_CASES=%d", cases))
	var out strings.Builder
	run.Stdout = &out
	run.Stderr = stderr
	runErr := run.Run()
	rows := out.String()
	fmt.Fprint(stdout, rows)
	code := 0
	if runErr != nil {
		if exit, isExit := runErr.(*exec.ExitError); isExit {
			code = exit.ExitCode()
		} else {
			fmt.Fprintf(stderr, "oak prove: %v\n", runErr)
			return 2
		}
	}
	if !crossCheck {
		return code
	}
	// The Go ladder on the same file, row by row.
	source, err := os.ReadFile(target)
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	model, err := compiler.New().WithSyntaxRewrite(prove.Obligations).WithSource(target, string(source)).Check().Get()
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	results, err := prove.Theorems(model, cases)
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	goStatus := map[string]prove.Status{}
	for _, r := range results {
		goStatus[r.Name] = r.Status
	}
	agreed, compared := 0, 0
	for _, line := range strings.Split(rows, "\n") {
		fields := strings.Fields(line)
		if len(fields) < 2 || !strings.HasSuffix(fields[1], ":") || fields[0] == "oak" {
			continue
		}
		name := strings.TrimSuffix(fields[1], ":")
		status, known := goStatus[name]
		if !known {
			continue
		}
		compared++
		if string(status) == fields[0] {
			agreed++
			continue
		}
		fmt.Fprintf(stdout, "oak prove: the Go ladder disagrees on %s: Go %s, Oak %s\n", name, status, fields[0])
		code = 1
	}
	fmt.Fprintf(stdout, "oak prove: the Go ladder agrees on %d of %d rows\n", agreed, compared)
	return code
}
