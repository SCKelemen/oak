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

// FindSolver locates the SAT solver the rung runs: the binary named by
// OAK_SAT_SOLVER, else `cadical` on PATH. Only CaDiCaL's LRAT interface is
// spoken (`--lrat --no-binary <cnf> <proof>`). The empty string means the
// rung is skipped, by name.
func FindSolver() string {
	if named := os.Getenv("OAK_SAT_SOLVER"); named != "" {
		if path, err := exec.LookPath(named); err == nil {
			return path
		}
		return ""
	}
	if path, err := exec.LookPath("cadical"); err == nil {
		return path
	}
	return ""
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
	outcome := SATOutcome{}
	scanner := bufio.NewScanner(bytes.NewReader(stdout.Bytes()))
	scanner.Buffer(make([]byte, 0, 1<<16), 1<<26)
	for scanner.Scan() {
		line := scanner.Text()
		switch {
		case strings.HasPrefix(line, "s SATISFIABLE"):
			outcome.Satisfiable = true
		case strings.HasPrefix(line, "s UNSATISFIABLE"):
			outcome.Unsatisfiable = true
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
		}
	}
	if outcome.Satisfiable == outcome.Unsatisfiable {
		if runErr != nil {
			return SATOutcome{}, fmt.Errorf("the solver gave no verdict: %v", runErr)
		}
		return SATOutcome{}, fmt.Errorf("the solver gave no verdict")
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
