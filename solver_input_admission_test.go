package main

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

// Exercise the compiled production entry points, including a terminal refused
// continuation. Malformed views must never read or publish stale term bits.
func TestOakProblemInputAdmission(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	files, err := filepath.Glob(filepath.Join("prove", "solver", "*.oak"))
	if err != nil {
		t.Fatal(err)
	}
	var fixture string
	for _, path := range files {
		b, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if filepath.Base(path) == "main.oak" {
			text := string(b)
			fixture = text[strings.Index(text, "xor_problem:"):strings.Index(text, "main: ()")]
			continue
		}
		if err := os.WriteFile(filepath.Join(dir, filepath.Base(path)), b, 0600); err != nil {
			t.Fatal(err)
		}
	}
	source := "package main\n" + fixture + `
refuse: (l: Layout, mem: [*]u32, p: []u32): () {
 assert(!problem_shape_valid(l, p))
 assert(solve(l, mem, p) == STATUS_UNSUPPORTED)
 assert(cnf_lower(l, mem, p) == NONE)
 solve_begin(l, mem)
 assert(solve_resume(l, mem, p, u32(1)) == STATUS_UNSUPPORTED)
 assert(solve_resume(l, mem, p, u32(4096)) == STATUS_UNSUPPORTED)
}
main: (): i32 {
 l: Layout = layout_for(u32(4096), u32(8))
 raw: c.Ptr = malloc(c.Size((l.total + REPLAY_WORDS) * u32(4)))
 assert(raw != c.null())
 unsafe {
  mem: Buffer[u32] = c.own[u32](raw, l.total + REPLAY_WORDS)
  good: [192]u32 = xor_problem(true)
  assert(problem_shape_valid(l, view(&good)))
  assert(solve(l, span(&mem), view(&good)) == STATUS_PROVEN)
  bad: [192]u32 = xor_problem(false)
  assert(solve(l, span(&mem), view(&bad)) == STATUS_REFUTED)
  // Active variables are independent inputs, even when the declared
  // source expression would become a tautology after aliasing two maps.
  bad = good
  bad[HEADER_WORDS + LEAF_WORDS + u32(1)] = bad[HEADER_WORDS + u32(1)]
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[HEADER_WORDS + u32(2)] = bad[HEADER_WORDS + u32(1)]
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[HEADER_WORDS + u32(1)] = CNF_VAR_KEY
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[HEADER_WORDS + u32(1)] = NONE
  refuse(l, span(&mem), view(&bad))
  // Arbitrary sparse/permuted IDs remain valid; no dense producer order
  // is assumed. Inactive leaf bits are ignored, including repeated zeros.
  leaf: u32 = 0
  while leaf < u32(2) {
   bit: u32 = 0
   while bit < u32(64) {
    bad[HEADER_WORDS + leaf * LEAF_WORDS + u32(1) + bit] = bit < u32(8) ? { u32(1000000000) - bit * u32(31) - leaf } | { u32(0) }
    bit = bit + u32(1)
   }
   leaf = leaf + u32(1)
  }
  assert(problem_shape_valid(l, view(&bad)))
  assert(solve(l, span(&mem), view(&bad)) == STATUS_PROVEN)
  // 1152 distinct IDs exercise the saturated-table radix fallback.
  large: [1280]u32
  i: u32 = 0
  while i < u32(192) { large[i] = good[i]; i = i + u32(1) }
  large[u32(4)] = u32(16)
  leaf = u32(0)
  while leaf < u32(2) {
   large[HEADER_WORDS + leaf * LEAF_WORDS] = u32(64)
   bit: u32 = 0
   while bit < u32(64) {
    large[HEADER_WORDS + leaf * LEAF_WORDS + u32(1) + bit] = bit * u32(2) + leaf
    bit = bit + u32(1)
   }
   leaf = leaf + u32(1)
  }
  i = u32(0)
  while i < u32(1024) {
   large[u32(179) + i] = u32(1000000000) - i * u32(17)
   i = i + u32(1)
  }
  assert(problem_shape_valid(l, view(&large)))
  // A duplicate beyond the first saturated scan must be found after split.
  saved: u32 = large[u32(1202)]
  large[u32(1202)] = large[u32(1100)]
  refuse(l, span(&mem), view(&large))
  large[u32(1202)] = CNF_VAR_KEY - u32(1)
  assert(problem_shape_valid(l, view(&large)))
  large[u32(1202)] = saved
  large[u32(179)] = u32(0)
  refuse(l, span(&mem), view(&large))
  large[u32(179)] = large[u32(180)]
  refuse(l, span(&mem), view(&large))
  large[u32(179)] = CNF_VAR_KEY
  refuse(l, span(&mem), view(&large))
  // A large dense select map checks that fixed scratch does not impose a
  // 1024-variable admission limit; the final duplicate requires full scans.
  dense: [65715]u32
  i = u32(0)
  while i < u32(192) { dense[i] = good[i]; i = i + u32(1) }
  dense[u32(4)] = u32(1024)
  i = u32(0)
  while i < u32(65536) { dense[u32(179) + i] = u32(1000) + i; i = i + u32(1) }
  assert(problem_shape_valid(l, view(&dense)))
  dense[u32(65714)] = dense[u32(65713)]
  refuse(l, span(&mem), view(&dense))
  stream_cancelled = true
  assert(!problem_shape_valid(l, view(&good)))
  assert(solve(l, span(&mem), view(&good)) == STATUS_CANCELLED)
  solve_begin(l, span(&mem))
  assert(solve_resume(l, span(&mem), view(&good), u32(1)) == STATUS_CANCELLED)
  assert(solve_resume(l, span(&mem), view(&good), u32(4096)) == STATUS_CANCELLED)
  stream_cancelled = false
  // Every truncation of the required 179-word fixture is refused.
  n: u32 = 0
  while n < u32(179) {
   good_view: []u32 = view(&good)
   refuse(l, span(&mem), subslice(good_view, u32(0), n))
   n = n + u32(1)
  }
  // Count arithmetic must widen before multiplying, adding, or indexing.
  field: u32 = 0
  while field < u32(5) {
   field != u32(3) ? {
    bad = good
    bad[field] = u32(4294967295)
    refuse(l, span(&mem), view(&bad))
   } | { }
   field = field + u32(1)
  }
  bad = good
  bad[2] = u32(0)
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[8] = u32(65)
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[8] = u32(0)
  refuse(l, span(&mem), view(&bad))
  base: u32 = HEADER_WORDS + u32(2) * LEAF_WORDS
  bad = good
  bad[base + u32(3)] = u32(2)
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[base + u32(2)] = u32(65)
  refuse(l, span(&mem), view(&bad))
  bad = good
  bad[base] = u32(8)
  refuse(l, span(&mem), view(&bad))
  // Self, forward, and out-of-range operand references.
  ref: u32 = 2
  while ref < u32(6) {
   bad = good
   bad[base + u32(2) * TERM_WORDS + u32(3)] = ref
   refuse(l, span(&mem), view(&bad))
   ref = ref + u32(1)
  }
  bad = good
  bad[base + u32(5) * TERM_WORDS] = u32(5)
  refuse(l, span(&mem), view(&bad))
  small: Layout = layout_for(u32(4096), u32(4))
  refuse(small, span(&mem), view(&good))
  free(c.disown(mem))
 }
 i32(0)
}
`
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	c, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	path, bin := filepath.Join(dir, "admission.c"), filepath.Join(dir, "admission")
	if err := os.WriteFile(path, []byte(c), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, path, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	started := time.Now()
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("problem admission: %v\n%s", err, out)
	}
	t.Logf("compiled admission corpus (including 65536 select IDs): %s", time.Since(started))
}
