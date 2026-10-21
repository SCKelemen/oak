package main

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

// Exercise production ownership paths, replacing only the allocator's FFI.
func TestOakSolverAllocationFailures(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for allocation failure regression")
	}
	dir := t.TempDir()
	files, err := filepath.Glob(filepath.Join("prove", "solver", "*.oak"))
	if err != nil {
		t.Fatal(err)
	}
	for _, path := range files {
		if filepath.Base(path) == "main.oak" {
			continue
		}
		b, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		s := string(b)
		if filepath.Base(path) == "driver.oak" {
			s = strings.ReplaceAll(s, `c.extern("malloc")`, `c.extern("lrat_test_malloc")`)
			s = strings.ReplaceAll(s, `c.extern("free")`, `c.extern("lrat_test_free")`)
		}
		if err := os.WriteFile(filepath.Join(dir, filepath.Base(path)), []byte(s), 0600); err != nil {
			t.Fatal(err)
		}
	}
	var source strings.Builder
	source.WriteString(`package main
reset_mask: (n: c.UInt32): () = c.extern("lrat_test_reset_mask")
calls: (): c.UInt32 = c.extern("lrat_test_calls")
outstanding: (): c.UInt32 = c.extern("lrat_test_live")
bad: (): c.UInt32 = c.extern("lrat_test_bad")
fixture_malloc: (n: c.Size): c.Ptr = c.extern("malloc")
fixture_free: (p: c.Ptr): () = c.extern("free")
main: (): i32 {
 p: [82]u32
 i: u32 = 0
 while i < u32(82) { p[i] = u32(0) i = i + u32(1) }
 p[0] = u32(1)
 p[1] = u32(1)
 p[2] = u32(1)
 p[3] = u32(16)
 p[8] = u32(1)
 p[75] = u32(1)
 lw: Lower = lower_layout(u32(0),u32(0))
 b0: c.Ptr = fixture_malloc(c.Size(lw.built_total * u32(4)))
 b1: c.Ptr = fixture_malloc(c.Size(lw.built_total * u32(4)))
 b2: c.Ptr = fixture_malloc(c.Size(lw.built_total * u32(4)))
 assert(b0 != c.null() && b1 != c.null() && b2 != c.null())
 unsafe {
  x0: Buffer[u32] = c.own[u32](b0,lw.built_total)
  x1: Buffer[u32] = c.own[u32](b1,lw.built_total)
  x2: Buffer[u32] = c.own[u32](b2,lw.built_total)
  k: u32 = 0
  while k < u32(82) {
   span(&x0)[k] = p[k]
   span(&x1)[k] = p[k]
   span(&x2)[k] = p[k]
   k = k + u32(1)
  }
  r0: c.Ptr = c.disown(x0)
  r1: c.Ptr = c.disown(x1)
  r2: c.Ptr = c.disown(x2)
 }
 l: Layout = layout_for(u32(16),u32(1))
 out: [520]u32
`)
	for variants := 1; variants <= 3; variants++ {
		for mask := 0; mask < 8; mask++ {
			fmt.Fprintf(&source, "reset_mask(c.UInt32(%d))\nout[0] = STATUS_PROVEN\nout[1] = u32(99)\nout[2] = u32(99)\nout[3] = u32(99)\nrace_in_oak(l,lw,b0,b1,b2,u32(82),u32(82),u32(82),u32(%d),span(&out))\n", mask, variants)
			if mask == 0 {
				source.WriteString("assert(out[0] == STATUS_REFUTED)\n")
			} else {
				source.WriteString("assert(out[0] == STATUS_EXCEEDED && out[1] == u32(0) && out[2] == u32(0) && out[3] == u32(0))\n")
			}
			source.WriteString("assert(u32(calls()) == u32(3) && u32(outstanding()) == u32(0) && u32(bad()) == u32(0))\n")
		}
	}
	for mask := 0; mask < 4; mask++ {
		fmt.Fprintf(&source, "reset_mask(c.UInt32(%d))\nout[0] = CERT_PROVEN\nout[1] = u32(99)\nout[3] = u32(99)\ncertify_over(view(&p),u32(82),u32(16),span(&out))\n", mask)
		if mask == 0 {
			source.WriteString("assert(out[0] == CERT_MODEL)\n")
		} else {
			source.WriteString("assert(out[0] == CERT_REFUSED && out[1] == u32(0) && out[3] == u32(0))\n")
		}
		calls := 2
		if mask&1 != 0 {
			calls = 1
		}
		fmt.Fprintf(&source, "assert(u32(calls()) == u32(%d) && u32(outstanding()) == u32(0) && u32(bad()) == u32(0))\n", calls)
	}
	source.WriteString("fixture_free(b2)\nfixture_free(b1)\nfixture_free(b0)\n0\n}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source.String()), 0600); err != nil {
		t.Fatal(err)
	}
	generated, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	cpath, shim, bin := filepath.Join(dir, "entry.c"), filepath.Join(dir, "alloc.c"), filepath.Join(dir, "entry")
	// The SAT arena has a fixed multi-megabyte floor; keep a deterministic cap.
	allocator := strings.Replace(lratAllocationShim, "n > 1048576", "n > 134217728", 1)
	for path, content := range map[string]string{cpath: generated, shim: allocator} {
		if err := os.WriteFile(path, []byte(content), 0600); err != nil {
			t.Fatal(err)
		}
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, shim, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("allocation failure: %v\n%s", err, out)
	}
	t.Log("checked all eight BDD allocation masks for one, two and three variants and all four CNF/SAT masks")
}
