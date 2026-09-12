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

// The theorem lowering written in Oak (asm/syntax.go serializes for it).
//
//go:embed prove/solver/lower.oak
var oakLoweringSource string

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

report: (index: u32, status: u32, nodes: u32, lowered: u32, vars: []u32, listed: u32): () {
  write_u32(index)
  write_byte(u8(32))
  write_u32(status)
  write_byte(u8(32))
  write_u32(nodes)
  write_byte(u8(32))
  write_u32(lowered)
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

solve_one: (l: Layout, mem: [*]u32, p: []u32, index: u32, lowered: u32): () {
  status: u32 = solve(l, mem, p)
  vars: [256]u32
  listed: u32 = status == STATUS_REFUTED ? { witness_vars(l, mem, p, span(&vars)) } | { u32(0) }
  report(index, status, node_count(l, mem), lowered, view(&vars), listed)
}

// dump_problem prints a built problem's words as a D line (index, count, words) when
// OAK_SOLVER_DUMP is set (a debugging aid: the Oak lowering's terms beside
// the Go lowering's).
dump_problem: (p: []u32, index: u32): () {
  flag: c.Ptr = c_getenv(c.cstr("OAK_SOLVER_DUMP\0"))
  wanted: Bool = false
  unsafe {
    value: []u8 = c.borrow_string(flag)
    wanted = len(value) > u32(0)
  }
  wanted ? {
    write_byte(u8(68))
    write_byte(u8(32))
    write_u32(index)
    write_byte(u8(32))
    write_u32(len(p))
    i: u32 = 0
    while i < len(p) {
      write_byte(u8(32))
      write_u32(p[i])
      i = i + u32(1)
    }
    write_byte(u8(10))
  } | { }
}

// leaf_bit_of finds the leaf and bit a variable of the problem stands for
// (leaf * 64 + bit), NONE for a select variable.
leaf_bit_of: (p: []u32, v: u32): u32 {
  leaves: u32 = problem_leaves(p)
  out: u32 = NONE
  li: u32 = 0
  while li < leaves && out == NONE {
    bit: u32 = 0
    while bit < u32(64) && out == NONE {
      out = p[HEADER_WORDS + li * LEAF_WORDS + u32(1) + bit] == v ? { li * u32(64) + bit } | { out }
      bit = bit + u32(1)
    }
    li = li + u32(1)
  }
  out
}

// solve_prefix solves the problem the Oak lowering built in the first n
// words of a view (the slice taken here, so the view ends with the call),
// reporting a refutation's witness as leaf and bit.
solve_prefix: (l: Layout, mem: [*]u32, whole: []u32, n: u32, index: u32): () {
  p: []u32 = subslice(whole, u32(0), n)
  dump_problem(p, index)
  status: u32 = solve(l, mem, p)
  vars: [256]u32
  listed: u32 = status == STATUS_REFUTED ? { witness_vars(l, mem, p, span(&vars)) } | { u32(0) }
  kept: u32 = 0
  i: u32 = 0
  while i < listed {
    lb: u32 = leaf_bit_of(p, vars[i])
    lb == NONE ? { } | {
      vars[kept] = lb
      kept = kept + u32(1)
    }
    i = i + u32(1)
  }
  report(index, status, node_count(l, mem), u32(1), view(&vars), kept)
}

// solve_variant solves one Go-lowered problem in a fresh view of the
// node table's memory.
solve_variant: (l: Layout, table_raw: c.Ptr, p: []u32, index: u32): () {
  unsafe {
    tbuf: Buffer[u32] = c.own[u32](table_raw, l.total)
    solve_one(l, span(&tbuf), p, index, u32(0))
    released: c.Ptr = c.disown(tbuf)
  }
}

// lower_in_oak runs the Oak lowering on a syntax table into the built
// buffer's memory; the problem's word count, 0 outside the subset.
lower_in_oak: (lw: Lower, work_raw: c.Ptr, built_raw: c.Ptr, sx: []u32, budget: u32, order: u32): u32 {
  n: u32 = 0
  unsafe {
    wbuf: Buffer[u32] = c.own[u32](work_raw, lw.total)
    bbuf: Buffer[u32] = c.own[u32](built_raw, lw.built_total)
    n = lower_theorem(lw, span(&wbuf), span(&bbuf), sx, budget, order)
    n = n == u32(0) ? { NONE - lower_reason(lw, span(&wbuf)) } | { n }
    released_w: c.Ptr = c.disown(wbuf)
    released_b: c.Ptr = c.disown(bbuf)
  }
  n
}

// solve_lowered solves the problem the Oak lowering built (n words at the
// built buffer's memory) and reports it as lowered in Oak.
solve_lowered: (l: Layout, lw: Lower, table_raw: c.Ptr, built_raw: c.Ptr, n: u32, index: u32): () {
  unsafe {
    tbuf: Buffer[u32] = c.own[u32](table_raw, l.total)
    bbuf: Buffer[u32] = c.own[u32](built_raw, lw.built_total)
    solve_prefix(l, span(&tbuf), view(&bbuf), n, index)
    released_t: c.Ptr = c.disown(tbuf)
    released_b: c.Ptr = c.disown(bbuf)
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
  lowered_terms: u32 = 131072
  terms_cap: u32 = max_terms > lowered_terms ? { max_terms } | { lowered_terms }
  l: Layout = layout_for(budget, terms_cap)
  lw: Lower = lower_layout(lowered_terms, u32(64))
  table_raw: c.Ptr = malloc(c.Size(l.total * u32(4)))
  work_raw: c.Ptr = malloc(c.Size(lw.total * u32(4)))
  built_raw: c.Ptr = malloc(c.Size(lw.built_total * u32(4)))
  unsafe {
    problem_bytes: Buffer[u8] = c.own[u8](bytes_raw, total * u32(4))
    words_ok: Bool = read_fully(chunk_raw, span(&problem_bytes), total * u32(4))
    stream: Buffer[u32] = c.own[u32](words_raw, total)
    words_of(view(&problem_bytes), span(&stream), total)
    words_ok ? { solve_stream(l, lw, view(&stream), table_raw, work_raw, built_raw, count, slot, budget) } | { }
    free(c.disown(stream))
    free(c.disown(problem_bytes))
  }
  free(table_raw)
  free(work_raw)
  free(built_raw)
  free(chunk_raw)
  i32_bits_u32(u32(0))
}

// solve_stream walks the problems stream: per theorem the Go-lowered
// variants and, when present, the syntax table. With a syntax table,
// slots 0, 1, and 2 lower it in Oak under the interleaved, blocked, and
// control-first orders and solve, and slot k solves Go-lowered variant
// k - 3; without, slot k solves variant k.
solve_stream: (l: Layout, lw: Lower, data: []u32, table_raw: c.Ptr, work_raw: c.Ptr, built_raw: c.Ptr, count: u32, slot: u32, budget: u32): () {
  off: u32 = 0
  i: u32 = 0
  while i < count {
    variants: u32 = data[off]
    off = off + u32(1)
    variant_start: u32 = off
    j: u32 = 0
    while j < variants {
      words: u32 = data[off]
      off = off + u32(1)
      off = off + words
      j = j + u32(1)
    }
    syntax_words: u32 = data[off]
    off = off + u32(1)
    syntax_start: u32 = off
    off = off + syntax_words
    shift: u32 = syntax_words > u32(0) ? { u32(3) } | { u32(0) }
    (syntax_words > u32(0) && slot < u32(3)) ? {
      n: u32 = lower_in_oak(lw, work_raw, built_raw, subslice(data, syntax_start, syntax_words), budget, slot)
      n < u32(0x80000000) ? { solve_lowered(l, lw, table_raw, built_raw, n, i) } | {
        none: [1]u32
        reason: u32 = NONE - n
        report(i, reason == REASON_ORDER ? { STATUS_EXCEEDED } | { STATUS_UNSUPPORTED }, reason, u32(1), view(&none), u32(0))
      }
    } | {
      want: u32 = slot - shift
      k: u32 = 0
      at: u32 = variant_start
      while k < variants {
        words_k: u32 = data[at]
        at = at + u32(1)
        k == want ? { solve_variant(l, table_raw, subslice(data, at, words_k), i) } | { }
        at = at + words_k
        k = k + u32(1)
      }
    }
    i = i + u32(1)
  }
}
`

// oakSolverBinary builds the solver program once per solver source, in a
// directory under the temporary directory named by the sources' hash,
// and returns the binary's path; a later run finds it built.
func oakSolverBinary() (string, error) {
	sum := sha256.Sum256([]byte(oakSolverSource + "\x00" + oakLoweringSource + "\x00" + oakSolverDriverSource))
	dir := filepath.Join(os.TempDir(), "oak-solver-"+hex.EncodeToString(sum[:6]))
	binary := filepath.Join(dir, "solver")
	if info, err := os.Stat(binary); err == nil && info.Mode().IsRegular() {
		return binary, nil
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return "", err
	}
	for name, text := range map[string]string{"oak.mod": "module oak.prove.solver\noak 0.1.0\n", "bdd.oak": oakSolverSource, "lower.oak": oakLoweringSource, "main.oak": oakSolverDriverSource} {
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
func encodeProblems(theorems []oakTheorem, budget int) []byte {
	maxTerms, total := 1, 0
	for _, th := range theorems {
		total += 2 + len(th.Syntax)
		for _, p := range th.Problems {
			total += 1 + len(p.Words)
			if p.Terms > maxTerms {
				maxTerms = p.Terms
			}
		}
	}
	words := make([]uint32, 0, 4+total)
	words = append(words, uint32(len(theorems)), uint32(maxTerms), uint32(budget), uint32(total))
	for _, th := range theorems {
		words = append(words, uint32(len(th.Problems)))
		for _, p := range th.Problems {
			words = append(words, uint32(len(p.Words)))
			words = append(words, p.Words...)
		}
		words = append(words, uint32(len(th.Syntax)))
		words = append(words, th.Syntax...)
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
// oakTheorem is one pending theorem: its Go-lowered problems, one per
// variable order, and its syntax table when the Oak lowering can take it.
type oakTheorem struct {
	Problems []asm.Problem
	Syntax   []uint32
}

// oakOrders is the number of variable orders the Oak lowering races when
// a theorem has a syntax table (interleaved, blocks, control), in slots
// 0 to 2, the Go-lowered variants following.
const oakOrders = 3

// slots is the number of solver processes the theorem's verdict can come
// from: its Go-lowered variants, plus the Oak lowering's orders when it
// applies.
func (th oakTheorem) slots() int {
	if len(th.Syntax) > 0 {
		return len(th.Problems) + oakOrders
	}
	return len(th.Problems)
}

func runOakSolver(theorems []oakTheorem, budget int) ([]prove.SolverVerdict, error) {
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
	for _, th := range theorems {
		if th.slots() > slots {
			slots = th.slots()
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
	oakLoweringDone := make([]bool, len(theorems))
	oakPending := make([]int, len(theorems)) // Oak orders yet to answer
	held := make([]*prove.SolverVerdict, len(theorems))
	remaining := len(theorems)
	var firstErr error
	for l := range lines {
		if strings.HasPrefix(l.text, "D ") {
			if dump := os.Getenv("OAK_SOLVER_DUMP"); dump != "" {
				f, _ := os.OpenFile(dump, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
				if f != nil {
					fmt.Fprintf(f, "slot %d %s\n", l.slot, l.text)
					f.Close()
				}
			}
			continue
		}
		v, index, err := parseOakVerdict(l.text)
		if err != nil {
			if firstErr == nil {
				firstErr = err
			}
			continue
		}
		// A slot the theorem has no variant for reports the budget exceeded
		// as a placeholder; only its own slots count.
		if index < 0 || index >= len(theorems) || settled[index] || l.slot >= theorems[index].slots() {
			continue
		}
		answered[index]++
		hasSyntax := len(theorems[index].Syntax) > 0
		isOak := hasSyntax && l.slot < oakOrders
		v.Winner = l.slot
		if hasSyntax {
			// Slots 0 to 2 are the Oak lowering's orders; the Go-lowered
			// variants follow.
			v.Winner = l.slot - oakOrders
		}
		if isOak {
			v.Winner = l.slot // the order
			if oakPending[index] == 0 {
				oakPending[index] = oakOrders
			}
		}
		decided := v.Status == 0 || v.Status == 1
		switch {
		case decided && (!hasSyntax || isOak || oakLoweringDone[index]):
			// The Oak lowering's verdict is preferred when it applies: a
			// Go-lowered verdict stands only once every Oak order has
			// answered without deciding.
			verdicts[index] = v
			settled[index] = true
			remaining--
		case decided:
			// A Go-lowered verdict ahead of the Oak lowering: held until the
			// Oak lowering's orders have answered.
			held[index] = &v
		default:
			// Unsupported outranks exceeded: the Go decider is then asked.
			if v.Status == 3 || failing[index] == 0 {
				failing[index] = v.Status
			}
			if isOak {
				oakPending[index]--
				if oakPending[index] == 0 {
					oakLoweringDone[index] = true
					if h := held[index]; h != nil {
						verdicts[index] = *h
						settled[index] = true
						remaining--
					}
				}
			}
			if !settled[index] && answered[index] == theorems[index].slots() {
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

// parseOakVerdict reads one `index status nodes lowered count vars...` line.
func parseOakVerdict(text string) (prove.SolverVerdict, int, error) {
	fields := strings.Fields(text)
	if len(fields) < 5 {
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
	index, status, nodes, lowered, listed := numbers[0], numbers[1], numbers[2], numbers[3], numbers[4]
	if len(numbers) != 5+listed {
		return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
	}
	v := prove.SolverVerdict{Status: status, Nodes: nodes, Lowered: lowered != 0}
	for _, x := range numbers[5:] {
		v.Vars = append(v.Vars, uint32(x))
	}
	return v, index, nil
}
