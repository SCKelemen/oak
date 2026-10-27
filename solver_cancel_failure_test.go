package main

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

func TestOakSolverCancellationAllocationFailure(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal(err)
	}
	driver, err := os.ReadFile(filepath.Join("prove", "solver", "driver.oak"))
	if err != nil {
		t.Fatal(err)
	}
	source := `package main
malloc: (n: c.Size): c.Ptr = c.extern("lrat_test_malloc")
free: (p: c.Ptr): () = c.extern("lrat_test_free")
c_pread: (fd: c.Int, p: c.Ptr, n: c.Size, off: c.Int64): c.Int64 = c.extern("cancel_test_pread")
reset: (fail: c.UInt32, result: c.Int64): () = c.extern("cancel_test_reset")
reads: (): c.UInt32 = c.extern("cancel_test_reads")
allocations: (): c.UInt32 = c.extern("lrat_test_calls")
outstanding: (): c.UInt32 = c.extern("lrat_test_live")
bad: (): c.UInt32 = c.extern("lrat_test_bad")
` + lratSourceRegion(t, string(driver), "stream_cancel_enabled:", "// Output is buffered:") + `
main: (): i32 {
 stream_cancel_enabled = true
 stream_cancel_index = u32(42)
 reset(c.UInt32(1), c.Int64(1))
 assert(!cancel_poll())
 assert(reads() == c.UInt32(0))
 assert(allocations() == c.UInt32(1))
 assert(outstanding() == c.UInt32(0))
 assert(bad() == c.UInt32(0))
 // A later poll may retry; allocation failure did not forge cancellation.
 reset(c.UInt32(0), c.Int64(-1))
 assert(!cancel_poll())
 assert(reads() == c.UInt32(1))
 assert(outstanding() == c.UInt32(0))
 reset(c.UInt32(0), c.Int64(0))
 assert(!cancel_poll())
 assert(reads() == c.UInt32(1))
 assert(outstanding() == c.UInt32(0))
 reset(c.UInt32(0), c.Int64(1))
 assert(cancel_poll())
 assert(cancel_poll())
 assert(reads() == c.UInt32(1))
 assert(allocations() == c.UInt32(1))
 assert(outstanding() == c.UInt32(0))
 assert(bad() == c.UInt32(0))
 stream_cancelled = false
 stream_cancel_enabled = false
 reset(c.UInt32(1), c.Int64(1))
 assert(!cancel_poll())
 assert(allocations() == c.UInt32(0))
 i32(0)
}
`
	generated, err := compiler.New().WithSource("cancel_failure.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	shim := lratAllocationShim + `
static uint32_t read_calls;
static int64_t read_result;
void cancel_test_reset(uint32_t fail,int64_t result) {lrat_test_reset(fail);read_calls=0;read_result=result;}
uint32_t cancel_test_reads(void) {return read_calls;}
int64_t cancel_test_pread(int fd,void *p,size_t n,int64_t off) {
 if(fd!=3 || !p || n!=1 || off!=42) abort();
 ++read_calls;
 if(read_result==1) *(unsigned char*)p=1;
 return read_result;
}
`
	dir := t.TempDir()
	cpath, spath, bin := filepath.Join(dir, "entry.c"), filepath.Join(dir, "shim.c"), filepath.Join(dir, "entry")
	for path, s := range map[string]string{cpath: generated, spath: shim} {
		if err := os.WriteFile(path, []byte(s), 0600); err != nil {
			t.Fatal(err)
		}
	}
	ctx, cancel := context.WithTimeout(t.Context(), time.Minute)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-o", bin, cpath, spath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("compile: %v\n%s", err, out)
	}
	if out, err := exec.CommandContext(ctx, bin).CombinedOutput(); err != nil {
		t.Fatalf("cancellation: %v\n%s", err, out)
	}
}
