package main

import (
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

func TestOakSolverStreamAdmission(t *testing.T) {
	solver, err := oakSolverBinary()
	if err != nil {
		t.Fatal(err)
	}
	encode := func(words []uint32) []byte {
		b := make([]byte, 4*len(words))
		for i, w := range words {
			binary.LittleEndian.PutUint32(b[4*i:], w)
		}
		return b
	}
	// One true constant, one root, one named theorem; no source files.
	p := []uint32{1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0}
	body := append([]uint32{0, 0, 1, uint32(len(p))}, p...)
	body = append(body, 1, uint32('x'))
	words := append([]uint32{1, 1, 4096, uint32(len(body))}, body...)
	good := encode(words)
	run := func(name string, input []byte, valid bool) {
		t.Helper()
		t.Run(name, func(t *testing.T) {
			ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
			defer cancel()
			cmd := exec.CommandContext(ctx, solver)
			cmd.Env = append(os.Environ(), "OAK_SOLVER_MODE=", "OAK_SOLVER_VARIANT=0", "OAK_SOLVER_CANCEL_FD=")
			cmd.Stdin = bytes.NewReader(input)
			out, err := cmd.CombinedOutput()
			if valid {
				if err != nil || !strings.HasPrefix(string(out), "0 0 ") {
					t.Fatalf("valid stream: %v: %s", err, out)
				}
			} else {
				e, ok := err.(*exec.ExitError)
				if !ok || e.ExitCode() != 2 || len(out) != 0 {
					t.Fatalf("malformed stream: %v: %q", err, out)
				}
			}
		})
	}
	run("valid", good, true)
	for n := 0; n < len(good); n++ {
		run(fmt.Sprintf("truncated-%d", n), good[:n], false)
	}
	run("trailing-byte", append(append([]byte{}, good...), 0), false)
	faults := map[string][2]uint32{
		"body-overflow": {3, ^uint32(0)}, "terms-overflow": {1, ^uint32(0)}, "budget-overflow": {2, ^uint32(0)},
		"file-count": {5, ^uint32(0)}, "variant-count": {6, ^uint32(0)}, "problem-size": {7, ^uint32(0)},
		"small-problem": {7, 1}, "understated-terms": {1, 0}, "name-overflow": {uint32(len(words) - 2), ^uint32(0)},
		"theorem-count": {0, 2},
	}
	for name, f := range faults {
		bad := append([]uint32{}, words...)
		bad[f[0]] = f[1]
		run(name, encode(bad), false)
	}
	// File metadata must fit both its input span and the widened parser arena.
	for _, n := range []uint32{^uint32(0), 67108864} {
		run(fmt.Sprintf("source-size-%d", n), encode([]uint32{0, 1, 4096, 3, 0, 1, n}), false)
	}
}

// Execute every allocation failure mask on an admitted empty stream. The
// allocator is the only substituted production dependency; reads use a fixed
// complete frame so allocation schedules are deterministic.
func TestOakSolverStreamAllocationFailures(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal(err)
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
			s = strings.ReplaceAll(s, `c.extern("read")`, `c.extern("stream_test_read")`)
		}
		if err := os.WriteFile(filepath.Join(dir, filepath.Base(path)), []byte(s), 0600); err != nil {
			t.Fatal(err)
		}
	}
	source := strings.Replace(oakSolverDriverSource, "main: (): i32 {", "driver_unused_main: (): i32 {", 1) + `
reset_stream: (mask: c.UInt32): () = c.extern("stream_test_reset")
outstanding: (): c.UInt32 = c.extern("lrat_test_live")
bad: (): c.UInt32 = c.extern("lrat_test_bad")
main: (): i32 {
 mask: u32 = 0
 while mask < u32(1024) {
  reset_stream(c.UInt32(mask))
  result: i32 = stream_main()
  assert(result == (mask == u32(0) ? { i32(0) } | { i32(3) }))
  assert(outstanding() == c.UInt32(0))
  assert(bad() == c.UInt32(0))
  mask = mask + u32(1)
 }
 i32(0)
}
`
	if err := os.WriteFile(filepath.Join(dir, "main.oak"), []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	generated, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	shim := strings.Replace(lratAllocationShim, "n > 1048576", "n > 536870912", 1) + `
#include <string.h>
static size_t stream_at;
static const unsigned char stream_bytes[24]={0,0,0,0, 1,0,0,0, 0,16,0,0, 2,0,0,0, 0,0,0,0, 0,0,0,0};
void stream_test_reset(uint32_t mask) {lrat_test_reset_mask(mask);stream_at=0;}
uint64_t stream_test_read(int fd,void *dest,size_t n) {
 if(fd!=0) abort();
 if(n>sizeof(stream_bytes)-stream_at) n=sizeof(stream_bytes)-stream_at;
 memcpy(dest,stream_bytes+stream_at,n);stream_at+=n;return n;
}
`
	cpath, spath, bin := filepath.Join(dir, "entry.c"), filepath.Join(dir, "shim.c"), filepath.Join(dir, "entry")
	for path, s := range map[string]string{cpath: generated, spath: shim} {
		if err := os.WriteFile(path, []byte(s), 0600); err != nil {
			t.Fatal(err)
		}
	}
	ctx, cancel := context.WithTimeout(t.Context(), 3*time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, spath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("compile: %v\n%s", err, out)
	}
	cmd := exec.CommandContext(ctx, bin)
	cmd.Env = append(os.Environ(), "OAK_SOLVER_CANCEL_FD=")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("failure masks: %v\n%s", err, out)
	}
}
