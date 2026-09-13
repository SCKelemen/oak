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

// oakSyntaxSource is the syntax serializer written in Oak
// (prove/solver/syntax.oak): the raw parse tree (asm/rawsyntax.go) to the
// syntax table the lowering reads.
//
//go:embed prove/solver/syntax.oak
var oakSyntaxSource string

// oakTreeSource is the lexer and parser written in Oak
// (prove/solver/tree.oak): a law file's bytes to the raw parse tree the
// serializer reads.
//
//go:embed prove/solver/tree.oak
var oakTreeSource string

// oakProtocolSource is the protocol lowering written in Oak
// (prove/solver/protocol.oak): a protocol declaration to the state and
// step types and the projected functions, as compiler/protocols.go builds.
//
//go:embed prove/solver/protocol.oak
var oakProtocolSource string

// oakShellSource is the prover's shell written in Oak
// (prove/solver/shell.oak): `oak prove` on a law file, file to rows.
//
//go:embed prove/solver/shell.oak
var oakShellSource string

// oakLeanSource is the Lean projection written in Oak
// (prove/solver/lean.oak): the theorems and what they reach, rendered to
// the text codegen/lean writes.
//
//go:embed prove/solver/lean.oak
var oakLeanSource string

// oakDriverHelpersSource holds the driver's shared helpers
// (prove/solver/driver.oak): externs, reports, stream reading, and the
// buffer-owning entry points around the Oak lowering.
//
//go:embed prove/solver/driver.oak
var oakDriverHelpersSource string

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

// lower_and_solve lowers the serialized syntax table (n_syn words of
// whole) under the slot's order and decides: the exhaustive rung when
// the domain fits the cases bound and the body has no loop (slot 0 alone;
// the other orders stand aside), else a witnessed refutation, the
// diagram's verdict, or the reason the lowering declined.
lower_and_solve: (l: Layout, lw: Lower, ser: Ser, ser_raw: c.Ptr, table_raw: c.Ptr, work_raw: c.Ptr, built_raw: c.Ptr, whole: []u32, n_syn: u32, budget: u32, slot: u32, index: u32, cases: u32): () {
  sx: []u32 = subslice(whole, u32(0), n_syn)
  dump_syntax(sx, index)
  witness: [512]u32
  none: [1]u32
  dom: [256]u64
  total: u64 = theorem_domain(sx, u64(cases), span(&dom))
  exhaustive: Bool = total != DOMAIN_INFINITE && !has_loop(sx)
  exhaustive ? {
    slot != u32(0) ? { report(index, STATUS_EXCEEDED, REASON_ORDER, u32(1), view(&none), u32(0)) } | {
      n: u32 = lower_in_oak(lw, work_raw, built_raw, sx, budget, slot, span(&witness), false)
      n < u32(0x80000000) ? {
        verdict: u32 = enumerate_in_oak(lw, work_raw, built_raw, sx, span(&dom), total, span(&witness))
        verdict == u32(7) ? {
          listed: u32 = witness[u32(0)]
          bits: []u32 = view(&witness)
          report_lowered(index, u32(7), u32(0), u32(1), subslice(bits, u32(1), listed), listed, ser, ser_raw)
        } | { report(index, verdict, u32_trunc_u64(total), u32(1), view(&none), u32(0)) }
      } | {
        reason: u32 = NONE - n
        report(index, STATUS_UNSUPPORTED, reason, u32(1), view(&none), u32(0))
      }
    }
  } | {
  n: u32 = lower_in_oak(lw, work_raw, built_raw, sx, budget, slot, span(&witness), true)
  n == WITNESSED ? {
    // A witness input refuted the theorem (or fired a trap): reported
    // with the input's set leaf bits, no diagram built.
    verdict: u32 = witness[u32(0)] / u32(65536)
    listed: u32 = witness[u32(0)] % u32(65536)
    bits: []u32 = view(&witness)
    report_lowered(index, verdict, u32(0), u32(1), subslice(bits, u32(1), listed), listed, ser, ser_raw)
  } | {
    n < u32(0x80000000) ? { solve_lowered(l, lw, table_raw, built_raw, n, index, ser, ser_raw) } | {
      reason: u32 = NONE - n
      report(index, reason == REASON_ORDER ? { STATUS_EXCEEDED } | { STATUS_UNSUPPORTED }, reason, u32(1), view(&none), u32(0))
    }
  } }
}

lower_serialized: (l: Layout, lw: Lower, ser: Ser, ser_raw: c.Ptr, table_raw: c.Ptr, work_raw: c.Ptr, built_raw: c.Ptr, out_raw: c.Ptr, n_syn: u32, budget: u32, slot: u32, index: u32, cases: u32): () {
  unsafe {
    obuf: Buffer[u32] = c.own[u32](out_raw, ser.out_total)
    lower_and_solve(l, lw, ser, ser_raw, table_raw, work_raw, built_raw, view(&obuf), n_syn, budget, slot, index, cases)
    released_o: c.Ptr = c.disown(obuf)
  }
}

// parse_files parses every source file of the stream (its leading files
// section: the count, then per file the byte count and the bytes, four per
// word) into the arena: word 0 the file count, then per file the table's
// offset, word count (0 when the file did not parse), and parse reason.
// Returns the stream offset where the theorems begin.
parse_files: (par: Par, par_raw: c.Ptr, data: []u32, arena: [*]u32): u32 {
  nfiles: u32 = data[u32(1)]
  arena[u32(0)] = nfiles
  off: u32 = 2
  at: u32 = u32(1) + nfiles * u32(3)
  f: u32 = 0
  unsafe {
    pbuf: Buffer[u32] = c.own[u32](par_raw, par.total)
    while f < nfiles {
      nbytes: u32 = data[off]
      off = off + u32(1)
      nwords: u32 = (nbytes + u32(3)) / u32(4)
      src: []u32 = subslice(data, off, nwords)
      cap: u32 = nbytes * u32(16) + u32(16384)
      n: u32 = parse_source(par, span(&pbuf), src, nbytes, arena, at, cap)
      arena[u32(1) + f * u32(3)] = at
      arena[u32(2) + f * u32(3)] = n
      arena[u32(3) + f * u32(3)] = parse_reason(par, span(&pbuf))
      at = at + cap
      off = off + nwords
      f = f + u32(1)
    }
    released_p: c.Ptr = c.disown(pbuf)
  }
  off
}

// files_arena_words: the arena the files section needs.
files_arena_words: (data: []u32): u32 {
  nfiles: u32 = data[u32(1)]
  total: u32 = u32(1) + nfiles * u32(3)
  off: u32 = 2
  f: u32 = 0
  while f < nfiles {
    nbytes: u32 = data[off]
    total = total + nbytes * u32(16) + u32(16384)
    off = off + u32(1) + (nbytes + u32(3)) / u32(4)
    f = f + u32(1)
  }
  total
}

// find_theorem finds the named theorem (its bytes in name, n of them) in
// the parsed files: the file's table offset and length and the function
// index, through out (3 words; word 3 the first parse failure's reason);
// false when no file declares it.
find_theorem: (arena: []u32, name: []u32, n: u32, out: [*]u32): Bool {
  nfiles: u32 = arena[u32(0)]
  found: Bool = false
  out[u32(3)] = u32(0)
  f: u32 = 0
  while f < nfiles && !found {
    at: u32 = arena[u32(1) + f * u32(3)]
    len_f: u32 = arena[u32(2) + f * u32(3)]
    (len_f == u32(0) && out[u32(3)] == u32(0)) ? { out[u32(3)] = arena[u32(3) + f * u32(3)] } | { }
    len_f > u32(0) ? {
      rx: []u32 = subslice(arena, at, len_f)
      fi: u32 = raw_find_function_named(rx, name, n)
      fi != NONE ? {
        out[u32(0)] = at
        out[u32(1)] = len_f
        out[u32(2)] = fi
        found = true
      } | { }
    } | { }
    f = f + u32(1)
  }
  found
}

// shell_mode: OAK_SOLVER_MODE=prove selects the prover's shell (shell.oak).
shell_mode: (): Bool {
  p: c.Ptr = c_getenv(c.cstr("OAK_SOLVER_MODE\0"))
  is_prove: Bool = false
  unsafe {
    value: []u8 = c.borrow_string(p)
    is_prove = len(value) == u32(5) && value[u32(0)] == u8(112) && value[u32(1)] == u8(114)
  }
  is_prove
}

main: (): i32 {
  shell_mode() ? { shell_main() } | { stream_main() }
}

stream_main: (): i32 {
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
  ser: Ser = ser_layout(u32(65536), u32(131072))
  ser_raw: c.Ptr = malloc(c.Size(ser.total * u32(4)))
  out_raw: c.Ptr = malloc(c.Size(ser.out_total * u32(4)))
  par: Par = par_layout()
  par_raw: c.Ptr = malloc(c.Size(par.total * u32(4)))
  unsafe {
    problem_bytes: Buffer[u8] = c.own[u8](bytes_raw, total * u32(4))
    words_ok: Bool = read_fully(chunk_raw, span(&problem_bytes), total * u32(4))
    stream: Buffer[u32] = c.own[u32](words_raw, total)
    words_of(view(&problem_bytes), span(&stream), total)
    arena_words: u32 = words_ok ? { files_arena_words(view(&stream)) } | { u32(1) }
    arena_raw: c.Ptr = malloc(c.Size(arena_words * u32(4)))
    tables: Buffer[u32] = c.own[u32](arena_raw, arena_words)
    theorems_at: u32 = words_ok ? { parse_files(par, par_raw, view(&stream), span(&tables)) } | { u32(0) }
    words_ok ? { solve_stream(l, lw, ser, ser_raw, out_raw, view(&stream), view(&tables), theorems_at, table_raw, work_raw, built_raw, count, slot, budget) } | { }
    free(c.disown(tables))
    free(c.disown(stream))
    free(c.disown(problem_bytes))
  }
  free(table_raw)
  free(work_raw)
  free(built_raw)
  free(ser_raw)
  free(out_raw)
  free(par_raw)
  free(chunk_raw)
  i32_bits_u32(u32(0))
}

// solve_stream walks the theorems of the stream (from theorems_at, after
// the files): per theorem the Go-lowered variants and the theorem's name.
// With source files parsed, slots 0, 1, and 2 find the theorem in a
// file's tree, serialize it, lower the syntax table in Oak under the
// interleaved, blocked, and control-first orders, and solve, and slot k
// solves Go-lowered variant k - 3; without files, slot k solves variant k.
solve_stream: (l: Layout, lw: Lower, ser: Ser, ser_raw: c.Ptr, out_raw: c.Ptr, data: []u32, arena: []u32, theorems_at: u32, table_raw: c.Ptr, work_raw: c.Ptr, built_raw: c.Ptr, count: u32, slot: u32, budget: u32): () {
  off: u32 = theorems_at
  cases: u32 = data[u32(0)]
  nfiles: u32 = arena[u32(0)]
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
    name_bytes: u32 = data[off]
    off = off + u32(1)
    name_words: u32 = (name_bytes + u32(3)) / u32(4)
    name_start: u32 = off
    off = off + name_words
    shift: u32 = nfiles > u32(0) ? { u32(3) } | { u32(0) }
    (nfiles > u32(0) && slot < u32(3)) ? {
      where: [4]u32
      none: [1]u32
      find_theorem(arena, subslice(data, name_start, name_words), name_bytes, span(&where)) ? {
        n_syn: u32 = serialize_in_oak(ser, ser_raw, out_raw, subslice(arena, where[u32(0)], where[u32(1)]), where[u32(2)])
        n_syn < u32(0x80000000) ? { lower_serialized(l, lw, ser, ser_raw, table_raw, work_raw, built_raw, out_raw, n_syn, budget, slot, i, cases) } | {
          report(i, STATUS_UNSUPPORTED, NONE - n_syn, u32(1), view(&none), u32(0))
        }
      } | {
        // No file parsed declares the theorem (a generated obligation, or
        // a file outside the parser's subset: its reason, else 400).
        report(i, STATUS_UNSUPPORTED, where[u32(3)] == u32(0) ? { u32(400) } | { where[u32(3)] }, u32(1), view(&none), u32(0))
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
	sum := sha256.Sum256([]byte(oakSolverSource + "\x00" + oakLoweringSource + "\x00" + oakSyntaxSource + "\x00" + oakTreeSource + "\x00" + oakProtocolSource + "\x00" + oakShellSource + "\x00" + oakLeanSource + "\x00" + oakDriverHelpersSource + "\x00" + oakSolverDriverSource))
	dir := filepath.Join(os.TempDir(), "oak-solver-"+hex.EncodeToString(sum[:6]))
	binary := filepath.Join(dir, "solver")
	if info, err := os.Stat(binary); err == nil && info.Mode().IsRegular() {
		return binary, nil
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return "", err
	}
	for name, text := range map[string]string{"oak.mod": "module oak.prove.solver\noak 0.1.0\n", "bdd.oak": oakSolverSource, "lower.oak": oakLoweringSource, "syntax.oak": oakSyntaxSource, "tree.oak": oakTreeSource, "protocol.oak": oakProtocolSource, "shell.oak": oakShellSource, "lean.oak": oakLeanSource, "driver.oak": oakDriverHelpersSource, "main.oak": oakSolverDriverSource} {
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
func encodeProblems(theorems []oakTheorem, sources [][]byte, cases, budget int) []byte {
	packed := func(b []byte) []uint32 {
		out := make([]uint32, (len(b)+3)/4)
		for i, c := range b {
			out[i/4] |= uint32(c) << (8 * uint(i%4))
		}
		return out
	}
	maxTerms, total := 1, 2
	for _, src := range sources {
		total += 1 + (len(src)+3)/4
	}
	for _, th := range theorems {
		total += 2 + (len(th.Name)+3)/4
		for _, p := range th.Problems {
			total += 1 + len(p.Words)
			if p.Terms > maxTerms {
				maxTerms = p.Terms
			}
		}
	}
	words := make([]uint32, 0, 4+total)
	words = append(words, uint32(len(theorems)), uint32(maxTerms), uint32(budget), uint32(total))
	// The cases bound of the exhaustive rung, then the files: the count,
	// then per file its byte count and bytes.
	words = append(words, uint32(cases), uint32(len(sources)))
	for _, src := range sources {
		words = append(words, uint32(len(src)))
		words = append(words, packed(src)...)
	}
	for _, th := range theorems {
		words = append(words, uint32(len(th.Problems)))
		for _, p := range th.Problems {
			words = append(words, uint32(len(p.Words)))
			words = append(words, p.Words...)
		}
		words = append(words, uint32(len(th.Name)))
		words = append(words, packed([]byte(th.Name))...)
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
// oakTheorem is one pending theorem: its name (the parser written in Oak
// finds it in the streamed source files) and its Go-lowered problems, one
// per variable order.
type oakTheorem struct {
	Name     string
	Problems []asm.Problem
}

// oakOrders is the number of variable orders the Oak lowering races when
// a theorem has a syntax table (interleaved, blocks, control), in slots
// 0 to 2, the Go-lowered variants following.
const oakOrders = 3

// slots is the number of solver processes the theorem's verdict can come
// from: its Go-lowered variants, plus the Oak lowering's orders when it
// applies.
// slots is the number of solver slots a theorem occupies: the Oak
// lowering's three orders when source files are streamed, then the
// Go-lowered variants.
func (th oakTheorem) slots(withSources bool) int {
	if withSources {
		return len(th.Problems) + oakOrders
	}
	return len(th.Problems)
}

func runOakSolver(theorems []oakTheorem, sources [][]byte, cases, budget int) ([]prove.SolverVerdict, error) {
	withSources := len(sources) > 0
	if len(theorems) == 0 {
		return nil, nil
	}
	solver, err := oakSolverBinary()
	if err != nil {
		return nil, err
	}
	encoded := encodeProblems(theorems, sources, cases, budget)
	if os.Getenv("OAK_SOLVER_KEEP") != "" {
		kept := filepath.Join(os.TempDir(), fmt.Sprintf("oak-problems-%d.bin", os.Getpid()))
		_ = os.WriteFile(kept, encoded, 0o644)
		fmt.Fprintf(os.Stderr, "oak solver: keeping %s (binary %s)\n", kept, solver)
	}
	slots := 1
	for _, th := range theorems {
		if th.slots(withSources) > slots {
			slots = th.slots(withSources)
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
		if strings.HasPrefix(l.text, "D ") || strings.HasPrefix(l.text, "S ") {
			if dump := os.Getenv("OAK_SOLVER_DUMP"); dump != "" {
				f, _ := os.OpenFile(dump, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o644)
				if f != nil {
					fmt.Fprintf(f, "slot %d %s\n", l.slot, l.text)
					f.Close()
				}
			}
			continue
		}
		if os.Getenv("OAK_SOLVER_TRACE") != "" {
			fmt.Fprintf(os.Stderr, "oak solver slot %d: %s\n", l.slot, l.text)
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
		if index < 0 || index >= len(theorems) || settled[index] || l.slot >= theorems[index].slots(withSources) {
			continue
		}
		answered[index]++
		hasSyntax := withSources
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
		// 4: a witness input trapped; 5 and 7: the exhaustive rung decided or
		// refuted; 6: the exhaustive rung's evaluation failed (the Go
		// interpreter's to explain, a decided verdict for the race).
		decided := v.Status == 0 || v.Status == 1 || v.Status == 4 || v.Status == 5 || v.Status == 6 || v.Status == 7
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
			if !settled[index] && answered[index] == theorems[index].slots(withSources) {
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
	// index status nodes lowered count vars... names...: the names are the
	// leaves of a theorem lowered in Oak, as its serializer sorted them.
	fields := strings.Fields(text)
	if len(fields) < 5 {
		return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
	}
	var numbers []int
	for _, f := range fields[:5] {
		n, err := strconv.Atoi(f)
		if err != nil {
			return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
		}
		numbers = append(numbers, n)
	}
	index, status, nodes, lowered, listed := numbers[0], numbers[1], numbers[2], numbers[3], numbers[4]
	if listed < 0 || len(fields) < 5+listed {
		return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
	}
	v := prove.SolverVerdict{Status: status, Nodes: nodes, Lowered: lowered != 0}
	for _, f := range fields[5 : 5+listed] {
		x, err := strconv.Atoi(f)
		if err != nil {
			return prove.SolverVerdict{}, -1, fmt.Errorf("oak solver: unreadable verdict %q", text)
		}
		v.Vars = append(v.Vars, uint32(x))
	}
	v.LeafNames = append(v.LeafNames, fields[5+listed:]...)
	return v, index, nil
}
