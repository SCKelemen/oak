package prove

// The certificate rung (docs/spec/125-verification.md §3, §4; the
// direction recorded in docs/notes/provers-2026-09.md): a bit-level
// obligation as clauses (asm.ExportCNF), an untrusted SAT solver run on
// them, and its LRAT certificate checked here (prove/lrat.go) and by the
// checker written in Oak (prove/solver/lrat.oak). The checkers settle the
// row; the solver's own verdict never does.

import (
	"bufio"
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
)

// CNFFor is the named theorem's obligation as clauses, restated for the
// decider as the ladder does. The reason names what refused the lowering.
func CNFFor(model *compiler.SemanticModel, name string) (asm.CNF, string, error) {
	stated, callees, guards, decls, reason, err := deciderInputs(model, name)
	if err != nil || reason != "" {
		return asm.CNF{}, reason, err
	}
	cnf, reason, ok := asm.ExportCNF(stated, callees, guards, decls)
	if !ok {
		return asm.CNF{}, reason, nil
	}
	return cnf, "", nil
}

// SATOutcome is what one solver run established: the verdict as the solver
// spoke it, the model when satisfiable, and the certificate text when
// unsatisfiable. Nothing here is trusted until the certificate is checked.
type SATOutcome struct {
	Unsatisfiable bool
	Satisfiable   bool
	Model         []int
	Certificate   string
}

// SolverTimeout bounds one solver run.
const SolverTimeout = 5 * time.Minute

// FindSolver locates an external SAT solver when OAK_SAT_SOLVER names one
// (a name on PATH or a path); the empty string means the rung uses the
// solver written in Oak. Only CaDiCaL's LRAT interface is spoken (`--lrat
// --no-binary <cnf> <proof>`). The second result is false when a named
// solver cannot be found, so the rung is skipped by name.
func FindSolver() (string, bool) {
	named := os.Getenv("OAK_SAT_SOLVER")
	if named == "" || named == "oak" {
		return "", true
	}
	if path, err := exec.LookPath(named); err == nil {
		return path, true
	}
	return "", false
}

// RunSolver writes the clauses to a temporary directory, runs the solver
// with an explicit argument list (no shell), and reads back the verdict
// line, the model, and the certificate file. The solver's output is
// untrusted text: it is parsed for the two verdict lines and integer
// model lines and nothing else.
func RunSolver(solver string, cnf asm.CNF, timeout time.Duration) (SATOutcome, error) {
	dir, err := os.MkdirTemp("", "oak-sat-")
	if err != nil {
		return SATOutcome{}, err
	}
	defer os.RemoveAll(dir)
	cnfPath := filepath.Join(dir, "obligation.cnf")
	proofPath := filepath.Join(dir, "obligation.lrat")
	if err := os.WriteFile(cnfPath, []byte(cnf.Text), 0o600); err != nil {
		return SATOutcome{}, err
	}
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()
	run := exec.CommandContext(ctx, solver, "--lrat", "--no-binary", cnfPath, proofPath)
	var stdout bytes.Buffer
	run.Stdout = &stdout
	run.Stderr = &bytes.Buffer{}
	runErr := run.Run()
	if ctx.Err() != nil {
		return SATOutcome{}, fmt.Errorf("the solver exceeded %s", timeout)
	}
	outcome, err := ParseSolverOutput(stdout.String(), false)
	if err != nil {
		if runErr != nil {
			return SATOutcome{}, fmt.Errorf("%v (%v)", err, runErr)
		}
		return SATOutcome{}, err
	}
	if outcome.Unsatisfiable {
		proof, err := os.ReadFile(proofPath)
		if err != nil {
			return SATOutcome{}, fmt.Errorf("the solver wrote no certificate: %v", err)
		}
		outcome.Certificate = string(proof)
	}
	return outcome, nil
}

// ParseSolverOutput reads a solver's text: the `s` verdict line, `v` model
// lines, and — when inline is set, as the solver written in Oak writes
// them — certificate lines, which begin with a digit. Anything else is
// ignored; a verdict of UNKNOWN or none is an error naming what was said.
func ParseSolverOutput(text string, inline bool) (SATOutcome, error) {
	if len(text) > lratLimit {
		return SATOutcome{}, fmt.Errorf("the solver's output exceeds %d bytes", lratLimit)
	}
	outcome := SATOutcome{}
	var certificate strings.Builder
	unknown := ""
	scanner := bufio.NewScanner(strings.NewReader(text))
	scanner.Buffer(make([]byte, 0, 1<<16), 1<<26)
	for scanner.Scan() {
		line := scanner.Text()
		switch {
		case strings.HasPrefix(line, "s SATISFIABLE"):
			outcome.Satisfiable = true
		case strings.HasPrefix(line, "s UNSATISFIABLE"):
			outcome.Unsatisfiable = true
		case strings.HasPrefix(line, "s UNKNOWN"):
			unknown = strings.TrimSpace(line)
		case strings.HasPrefix(line, "v "):
			for _, word := range strings.Fields(line[2:]) {
				lit, err := strconv.Atoi(word)
				if err != nil {
					return SATOutcome{}, fmt.Errorf("the solver's model line is not integers: %q", word)
				}
				if lit != 0 {
					outcome.Model = append(outcome.Model, lit)
				}
			}
		case inline && len(line) > 0 && line[0] >= '0' && line[0] <= '9':
			certificate.WriteString(line)
			certificate.WriteByte('\n')
		}
	}
	if outcome.Satisfiable == outcome.Unsatisfiable {
		if unknown != "" {
			return SATOutcome{}, fmt.Errorf("the solver gave up (%s)", unknown)
		}
		return SATOutcome{}, fmt.Errorf("the solver gave no verdict")
	}
	if inline && outcome.Unsatisfiable {
		outcome.Certificate = certificate.String()
	}
	return outcome, nil
}
