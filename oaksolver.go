package main

import (
	"bufio"
	"bytes"
	_ "embed"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	oaktarget "github.com/SCKelemen/oak/target"
)

// The bit-level solver written in Oak (docs/spec/125-verification.md
// section 7): the twin of asm/blast.go the prover runs beside it under
// `oak prove -solver oak`.
//
//go:embed prove/solver/bdd.oak
var oakSolverSource string

// oakVerdict is one problem's outcome from the Oak solver: the status
// (0 proven, 1 refuted, 2 budget exceeded, 3 unsupported) and the node
// count.
type oakVerdict struct {
	Status int
	Nodes  int
}

// runOakSolver compiles the Oak solver with the problems embedded as
// constant tables and a driver that solves each in turn, runs it on the
// host, and reads the verdicts back, one per problem in order.
func runOakSolver(problems []asm.Problem, budget int) ([]oakVerdict, error) {
	if len(problems) == 0 {
		return nil, nil
	}
	dir, err := os.MkdirTemp("", "oak-solver-*")
	if err != nil {
		return nil, err
	}
	if os.Getenv("OAK_SOLVER_KEEP") != "" {
		fmt.Fprintf(os.Stderr, "oak solver: keeping %s\n", dir)
	} else {
		defer os.RemoveAll(dir)
	}
	if err := os.WriteFile(filepath.Join(dir, "oak.mod"), []byte("module oak.prove.solver\noak 0.1.0\n"), 0o644); err != nil {
		return nil, err
	}
	if err := os.WriteFile(filepath.Join(dir, "bdd.oak"), []byte(oakSolverSource), 0o644); err != nil {
		return nil, err
	}
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(oakSolverDriver(problems, budget)), 0o644); err != nil {
		return nil, err
	}
	binary := filepath.Join(dir, "solver")
	host := oaktarget.Host()
	comp := compiler.New().WithPackageDir(dir)
	if err := compileBinary(comp, binary, defaultAsmMode(host), host, ""); err != nil {
		return nil, fmt.Errorf("oak solver: %v", err)
	}
	var out bytes.Buffer
	run := exec.Command(binary)
	run.Stdout, run.Stderr = &out, os.Stderr
	if err := run.Run(); err != nil {
		return nil, fmt.Errorf("oak solver: %v", err)
	}
	return parseOakVerdicts(&out, len(problems))
}

func parseOakVerdicts(r io.Reader, count int) ([]oakVerdict, error) {
	verdicts := make([]oakVerdict, count)
	seen := 0
	scanner := bufio.NewScanner(r)
	for scanner.Scan() {
		var index, status, nodes int
		if _, err := fmt.Sscanf(scanner.Text(), "%d %d %d", &index, &status, &nodes); err != nil || index < 0 || index >= count {
			return nil, fmt.Errorf("oak solver: unreadable verdict %q", scanner.Text())
		}
		verdicts[index] = oakVerdict{Status: status, Nodes: nodes}
		seen++
	}
	if seen != count {
		return nil, fmt.Errorf("oak solver: %d verdicts for %d problems", seen, count)
	}
	return verdicts, nil
}

// oakSolverDriver writes the driver package: every problem as a constant
// word table, and a main that sizes one buffer for the budget and the
// largest term count, solves each problem, and prints `index status nodes`.
func oakSolverDriver(problems []asm.Problem, budget int) string {
	var b strings.Builder
	b.WriteString("package main\n\nimport(\"host\")\n\n")
	b.WriteString("malloc: (n: c.Size): c.Ptr = c.extern(\"malloc\")\nfree: (p: c.Ptr): () = c.extern(\"free\")\n\n")
	maxTerms := 1
	for i, p := range problems {
		if p.Terms > maxTerms {
			maxTerms = p.Terms
		}
		fmt.Fprintf(&b, "P%d: [%d]u32 = [%d]u32{", i, len(p.Words), len(p.Words))
		for k, w := range p.Words {
			if k > 0 {
				b.WriteByte(',')
			}
			if k%32 == 0 {
				b.WriteByte('\n')
			}
			fmt.Fprintf(&b, " %d", w)
		}
		b.WriteString(" }\n\n")
	}
	b.WriteString(`write_u32: (v: u32): () {
  buf: [12]u8
  start: u32 = 12
  n: u32 = v
  start = start - u32(1)
  buf[start] = u8(48) + u8_trunc_u32(n % u32(10))
  n = n / u32(10)
  while n > u32(0) {
    start = start - u32(1)
    buf[start] = u8(48) + u8_trunc_u32(n % u32(10))
    n = n / u32(10)
  }
  digits: []u8 = view(&buf)
  host.host_write_all(host.host_stdout(), subslice(digits, start, u32(12) - start)) ? { } | { }
}

write_byte: (v: u8): () {
  one: [1]u8 = [1]u8{ v }
  host.host_write_all(host.host_stdout(), view(&one)) ? { } | { }
}

report: (index: u32, status: u32, nodes: u32): () {
  write_u32(index)
  write_byte(u8(32))
  write_u32(status)
  write_byte(u8(32))
  write_u32(nodes)
  write_byte(u8(10))
}

`)
	fmt.Fprintf(&b, "main: (): i32 {\n  l: Layout = layout_for(u32(%d), u32(%d))\n", budget, maxTerms)
	b.WriteString("  raw: c.Ptr = malloc(c.Size(l.total * u32(4)))\n  unsafe {\n    mem: Buffer[u32] = c.own[u32](raw, l.total)\n")
	for i := range problems {
		fmt.Fprintf(&b, "    s%d: u32 = solve(l, span(&mem), view(&P%d))\n    report(u32(%d), s%d, node_count(l, span(&mem)))\n", i, i, i, i)
	}
	b.WriteString("    free(c.disown(mem))\n  }\n  i32_bits_u32(u32(0))\n}\n")
	return b.String()
}
