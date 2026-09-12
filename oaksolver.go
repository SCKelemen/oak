package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	_ "embed"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
	oaktarget "github.com/SCKelemen/oak/target"
)

// The bit-level solver written in Oak (docs/spec/125-verification.md
// section 7): the twin of asm/blast.go the prover runs beside it under
// `oak prove -solver oak`.
//
//go:embed prove/solver/bdd.oak
var oakSolverSource string

// oakSolverDriverSource is the driver around the solver: it reads its
// order slot from OAK_SOLVER_VARIANT and the problems from its standard
// input (a header of count, largest term count, budget, and word total,
// then per theorem the variant count and per variant the word count and
// the words), solves each theorem's problem in its slot,
// and prints `index status nodes count vars...`, the vars those set on a
// failing path when the theorem is refuted. The program is the same for
// every run, so its binary is built once and kept.
const oakSolverDriverSource = `package main

import("host")

malloc: (n: c.Size): c.Ptr = c.extern("malloc")
free: (p: c.Ptr): () = c.extern("free")
c_getenv: (name: c.String): c.Ptr = c.extern("getenv")
c_read: (fd: c.Int, buf: c.Ptr, n: c.Size): c.UInt64 = c.extern("read")

write_u32: (v: u32): () {
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

report: (index: u32, status: u32, nodes: u32, vars: []u32, listed: u32): () {
  write_u32(index)
  write_byte(u8(32))
  write_u32(status)
  write_byte(u8(32))
  write_u32(nodes)
  write_byte(u8(32))
  write_u32(listed)
  i: u32 = 0
  while i < listed {
    write_byte(u8(32))
    write_u32(vars[i])
    i = i + u32(1)
  }
  write_byte(u8(10))
}

// The order slot this process solves: the first digit of OAK_SOLVER_VARIANT.
variant_slot: (): u32 {
  p: c.Ptr = c_getenv(c.cstr("OAK_SOLVER_VARIANT\0"))
  slot: u32 = 0
  unsafe {
    value: []u8 = c.borrow_string(p)
    slot = (len(value) > u32(0) && value[u32(0)] >= u8(48) && value[u32(0)] <= u8(57)) ? { u32(value[u32(0)] - u8(48)) } | { u32(0) }
  }
  slot
}

copy_header: (h: []u32): [4]u32 {
  out: [4]u32
  i: u32 = 0
  while i < u32(4) && i < len(h) {
    out[i] = h[i]
    i = i + u32(1)
  }
  out
}

solve_one: (l: Layout, mem: [*]u32, p: []u32, index: u32): () {
  status: u32 = solve(l, mem, p)
  vars: [256]u32
  listed: u32 = status == STATUS_REFUTED ? { witness_vars(l, mem, p, span(&vars)) } | { u32(0) }
  report(index, status, node_count(l, mem), view(&vars), listed)
}

CHUNK: u32 = 65536

// copy_chunk copies a chunk just read into the destination bytes.
copy_chunk: (chunk: []u8, got: u32, dest: [*]u8, at: u32): () {
  i: u32 = 0
  while i < got {
    dest[at + i] = chunk[i]
    i = i + u32(1)
  }
}

// read_fully reads n bytes from standard input into dest, chunk by chunk
// (a pipe delivers what it has); false when the input ends early.
read_fully: (chunk_raw: c.Ptr, dest: [*]u8, n: u32): Bool {
  done: u32 = 0
  ok: Bool = true
  while done < n && ok {
    want: u32 = n - done < CHUNK ? { n - done } | { CHUNK }
    got: u64 = u64(c_read(c.Int(0), chunk_raw, c.Size(want)))
    ok = got > u64(0) && got <= u64(want)
    ok ? {
      unsafe {
        chunk: Buffer[u8] = c.own[u8](chunk_raw, CHUNK)
        copy_chunk(view(&chunk), u32_trunc_u64(got), dest, done)
        released: c.Ptr = c.disown(chunk)
      }
      done = done + u32_trunc_u64(got)
    } | { }
  }
  ok
}

// words_of assembles little-endian words from the bytes read.
words_of: (bytes: []u8, words: [*]u32, count: u32): () {
  i: u32 = 0
  while i < count {
    words[i] = u32(bytes[i * u32(4)]) | (u32(bytes[i * u32(4) + u32(1)]) << u32(8)) | (u32(bytes[i * u32(4) + u32(2)]) << u32(16)) | (u32(bytes[i * u32(4) + u32(3)]) << u32(24))
    i = i + u32(1)
  }
}

main: (): i32 {
  slot: u32 = variant_slot()
  chunk_raw: c.Ptr = malloc(c.Size(CHUNK))
  header_bytes_raw: c.Ptr = malloc(c.Size(u32(16)))
  header_words_raw: c.Ptr = malloc(c.Size(u32(16)))
  count: u32 = 0
  max_terms: u32 = 1
  budget: u32 = 0
  total: u32 = 0
  unsafe {
    header_bytes: Buffer[u8] = c.own[u8](header_bytes_raw, u32(16))
    header_ok: Bool = read_fully(chunk_raw, span(&header_bytes), u32(16))
    header_words: Buffer[u32] = c.own[u32](header_words_raw, u32(4))
    words_of(view(&header_bytes), span(&header_words), u32(4))
    h: [4]u32 = copy_header(view(&header_words))
    count = header_ok ? { h[u32(0)] } | { u32(0) }
    max_terms = h[u32(1)]
    budget = h[u32(2)]
    total = h[u32(3)]
    free(c.disown(header_words))
    free(c.disown(header_bytes))
  }
  bytes_raw: c.Ptr = malloc(c.Size(total * u32(4)))
  words_raw: c.Ptr = malloc(c.Size(total * u32(4)))
  l: Layout = layout_for(budget, max_terms)
  raw: c.Ptr = malloc(c.Size(l.total * u32(4)))
  unsafe {
    problem_bytes: Buffer[u8] = c.own[u8](bytes_raw, total * u32(4))
    words_ok: Bool = read_fully(chunk_raw, span(&problem_bytes), total * u32(4))
    problems: Buffer[u32] = c.own[u32](words_raw, total)
    words_of(view(&problem_bytes), span(&problems), total)
    table: Buffer[u32] = c.own[u32](raw, l.total)
    words_ok ? { solve_all(l, span(&table), view(&problems), count, slot) } | { }
    free(c.disown(table))
    free(c.disown(problems))
    free(c.disown(problem_bytes))
  }
  free(chunk_raw)
  i32_bits_u32(u32(0))
}

// solve_all walks the problems file and solves every theorem's variant in
// this process's slot.
solve_all: (l: Layout, mem: [*]u32, data: []u32, count: u32, slot: u32): () {
  off: u32 = 0
  i: u32 = 0
  while i < count {
    variants: u32 = data[off]
    off = off + u32(1)
    j: u32 = 0
    while j < variants {
      words: u32 = data[off]
      off = off + u32(1)
      j == slot ? { solve_one(l, mem, subslice(data, off, words), i) } | { }
      off = off + words
      j = j + u32(1)
    }
    i = i + u32(1)
  }
}
`

// oakSolverBinary builds the solver program once per solver source, in a
// directory under the temporary directory named by the sources' hash,
// and returns the binary's path; a later run finds it built.
func oakSolverBinary() (string, error) {
	sum := sha256.Sum256([]byte(oakSolverSource + "\x00" + oakSolverDriverSource))
	dir := filepath.Join(os.TempDir(), "oak-solver-"+hex.EncodeToString(sum[:6]))
	binary := filepath.Join(dir, "solver")
	if info, err := os.Stat(binary); err == nil && info.Mode().IsRegular() {
		return binary, nil
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return "", err
	}
	for name, text := range map[string]string{"oak.mod": "module oak.prove.solver\noak 0.1.0\n", "bdd.oak": oakSolverSource, "main.oak": oakSolverDriverSource} {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(text), 0o644); err != nil {
			return "", err
		}
	}
	host := oaktarget.Host()
	staging := fmt.Sprintf("%s.%d", binary, os.Getpid())
	if err := compileBinary(compiler.New().WithPackageDir(dir), staging, defaultAsmMode(host), host, ""); err != nil {
		return "", fmt.Errorf("oak solver: %v", err)
	}
	if err := os.Rename(staging, binary); err != nil {
		return "", err
	}
	return binary, nil
}

// encodeProblems writes the problems file the driver reads.
func encodeProblems(theorems [][]asm.Problem, budget int) []byte {
	maxTerms, total := 1, 0
	for _, variants := range theorems {
		total++
		for _, p := range variants {
			total += 1 + len(p.Words)
			if p.Terms > maxTerms {
				maxTerms = p.Terms
			}
		}
	}
	words := make([]uint32, 0, 4+total)
	words = append(words, uint32(len(theorems)), uint32(maxTerms), uint32(budget), uint32(total))
	for _, variants := range theorems {
		words = append(words, uint32(len(variants)))
		for _, p := range variants {
			words = append(words, uint32(len(p.Words)))
			words = append(words, p.Words...)
		}
	}
	buf := make([]byte, 4*len(words))
	for i, w := range words {
		binary.LittleEndian.PutUint32(buf[4*i:], w)
	}
	return buf
}

// runOakSolver solves every theorem's problems with the Oak solver: the
// problems go to a file, and one process per order slot (chosen by
// OAK_SOLVER_VARIANT) works through them, each theorem taking the first
// verdict within budget among its own slots — the race the Go decider
// runs across goroutines, run across processes, so a theorem that is
// small under one order is decided in that order's time and the others
// are stopped.
func runOakSolver(theorems [][]asm.Problem, budget int) ([]prove.SolverVerdict, error) {
	if len(theorems) == 0 {
		return nil, nil
	}
	solver, err := oakSolverBinary()
	if err != nil {
		return nil, err
	}
	encoded := encodeProblems(theorems, budget)
	if os.Getenv("OAK_SOLVER_KEEP") != "" {
		kept := filepath.Join(os.TempDir(), fmt.Sprintf("oak-problems-%d.bin", os.Getpid()))
		_ = os.WriteFile(kept, encoded, 0o644)
		fmt.Fprintf(os.Stderr, "oak solver: keeping %s (binary %s)\n", kept, solver)
	}
	slots := 1
	for _, variants := range theorems {
		if len(variants) > slots {
			slots = len(variants)
		}
	}
	type line struct {
		slot int
		text string
	}
	lines := make(chan line, 64)
	var processes []*exec.Cmd
	var readers sync.WaitGroup
	for slot := 0; slot < slots; slot++ {
		run := exec.Command(solver)
		run.Env = append(os.Environ(), fmt.Sprintf("OAK_SOLVER_VARIANT=%d", slot))
		run.Stdin = bytes.NewReader(encoded)
		run.Stderr = os.Stderr
		out, err := run.StdoutPipe()
		if err != nil {
			return nil, err
		}
		if err := run.Start(); err != nil {
			return nil, fmt.Errorf("oak solver: %v", err)
		}
		processes = append(processes, run)
		readers.Add(1)
		go func(slot int, out io.Reader) {
			defer readers.Done()
			scanner := bufio.NewScanner(out)
			scanner.Buffer(make([]byte, 0, 1<<16), 1<<24)
			for scanner.Scan() {
				lines <- line{slot, scanner.Text()}
			}
		}(slot, out)
	}
	go func() {
		readers.Wait()
		close(lines)
	}()
	verdicts := make([]prove.SolverVerdict, len(theorems))
	settled := make([]bool, len(theorems))
	answered := make([]int, len(theorems)) // applicable slots heard from
	failing := make([]int, len(theorems))  // 2 exceeded, 3 unsupported among them
	remaining := len(theorems)
	var firstErr error
	for l := range lines {
		v, index, err := parseOakVerdict(l.text)
		if err != nil {
			if firstErr == nil {
				firstErr = err
			}
			continue
		}
		// A slot the theorem has no variant for reports the budget exceeded
		// as a placeholder; only its own slots count.
		if index < 0 || index >= len(theorems) || settled[index] || l.slot >= len(theorems[index]) {
			continue
		}
		answered[index]++
		v.Winner = l.slot
		switch {
		case v.Status == 0 || v.Status == 1:
			verdicts[index] = v
			settled[index] = true
			remaining--
		default:
			// Unsupported outranks exceeded: the Go decider is then asked.
			if v.Status == 3 || failing[index] == 0 {
				failing[index] = v.Status
			}
			if answered[index] == len(theorems[index]) {
				verdicts[index] = prove.SolverVerdict{Status: failing[index], Winner: -1}
				settled[index] = true
				remaining--
			}
		}
		if remaining == 0 {
			break
		}
	}
	for _, run := range processes {
		_ = run.Process.Kill()
	}
	for _, run := range processes {
		_ = run.Wait()
	}
	for range lines {
	}
	if remaining != 0 {
		if firstErr != nil {
			return nil, firstErr
		}
		return nil, fmt.Errorf("oak solver: %d theorems without a verdict", remaining)
	}
	return verdicts, nil
}

// parseOakVerdict reads one `index status nodes count vars...` line.
func parseOakVerdict(text string) (prove.SolverVerdict, int, error) {
	fields := strings.Fields(text)
	if len(fields) < 4 {
		return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
	}
	var numbers []int
	for _, f := range fields {
		n, err := strconv.Atoi(f)
		if err != nil {
			return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
		}
		numbers = append(numbers, n)
	}
	index, status, nodes, listed := numbers[0], numbers[1], numbers[2], numbers[3]
	if len(numbers) != 4+listed {
		return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
	}
	v := prove.SolverVerdict{Status: status, Nodes: nodes}
	for _, x := range numbers[4:] {
		v.Vars = append(v.Vars, uint32(x))
	}
	return v, index, nil
}
