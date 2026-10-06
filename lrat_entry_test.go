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
	"github.com/SCKelemen/oak/prove"
)

// Inject failure at every allocation site and count outstanding allocations.
// Large requests fail deterministically, so hostile headers cannot exhaust the
// test host. The production Oak allocation/free/ownership code is unchanged.
const lratAllocationShim = `
#include <stdint.h>
#include <stdlib.h>
static uint32_t calls, live, fail_at, bad;
void lrat_test_reset(uint32_t n) {
  if (live) abort();
  calls = bad = 0; fail_at = n;
}
void *lrat_test_malloc(size_t n) {
  ++calls;
  if (!n) ++bad;
  if (calls == fail_at || n > 1048576) return NULL;
  void *p = malloc(n);
  if (p) ++live;
  return p;
}
void lrat_test_free(void *p) { if (p) { --live; free(p); } }
uint32_t lrat_test_calls(void) { return calls; }
uint32_t lrat_test_live(void) { return live; }
uint32_t lrat_test_bad(void) { return bad; }
`

const lratAllocationExterns = `package main
malloc: (n: c.Size): c.Ptr = c.extern("lrat_test_malloc")
free: (p: c.Ptr): () = c.extern("lrat_test_free")
reset: (n: c.UInt32): () = c.extern("lrat_test_reset")
calls: (): c.UInt32 = c.extern("lrat_test_calls")
outstanding: (): c.UInt32 = c.extern("lrat_test_live")
bad: (): c.UInt32 = c.extern("lrat_test_bad")
`

func lratSourceRegion(t *testing.T, source, begin, end string) string {
	t.Helper()
	a, b := strings.Index(source, begin), strings.Index(source, end)
	if a < 0 || b <= a {
		t.Fatalf("cannot locate production source region %q .. %q", begin, end)
	}
	return source[a:b]
}

func lratEntryBinary(t *testing.T, source string) string {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler for LRAT entry-point tests")
	}
	generated, err := compiler.New().WithSource("lrat_entry.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	cpath, shim, bin := filepath.Join(dir, "entry.c"), filepath.Join(dir, "alloc.c"), filepath.Join(dir, "entry")
	for path, content := range map[string]string{cpath: generated, shim: lratAllocationShim} {
		if err := os.WriteFile(path, []byte(content), 0600); err != nil {
			t.Fatal(err)
		}
	}
	if out, err := exec.Command(cc, "-std=c99", "-O1", "-o", bin, cpath, shim).CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	return bin
}

func lratEntryRun(t *testing.T, bin string, input []byte) string {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, bin)
	cmd.Stdin = bytes.NewReader(input)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("LRAT entry: %v (%v)\n%s", err, ctx.Err(), out)
	}
	return string(out)
}

func lratEntryWords(name string, words []uint32) string {
	var out strings.Builder
	fmt.Fprintf(&out, "%s: [%d]u32\n", name, max(1, len(words)))
	for i, w := range words {
		fmt.Fprintf(&out, "%s[u32(%d)] = u32(%d)\n", name, i, w)
	}
	return out.String()
}

func TestOakLRATAllocatedEntry(t *testing.T) {
	base := formulaBindingCases(t)[0]
	var source strings.Builder
	source.WriteString(lratAllocationExterns + oakLRATSource)
	source.WriteString(lratSourceRegion(t, oakCertifySource, "lrat_check_record:", "// write_words_file"))
	source.WriteString("main: (): i32 {\n")
	// A valid record must accept normally and refuse all six injected failures.
	// Short output spans must not be written or cause any allocation at all.
	for fail := 0; fail <= 6; fail++ {
		for outLen := 0; outLen <= 3; outLen++ {
			source.WriteString("true ? {\n" + lratEntryWords("f", base.formula) + lratEntryWords("r", base.record))
			fmt.Fprintf(&source, "reset(c.UInt32(%d))\nout: [4]u32 = [4]u32{99, 99, 99, 99}\n", fail)
			fmt.Fprintf(&source, "s: u32 = lrat_check_record(view(&f), view(&r), span(&out)[0:u32(%d)])\n", outLen)
			want := 7
			if outLen == 3 && fail == 0 {
				want = 0
			}
			fmt.Fprintf(&source, "assert(s == u32(%d))\nassert(out[3] == 99)\n", want)
			if outLen < 3 {
				source.WriteString("assert(out[0] == 99 && out[1] == 99 && out[2] == 99)\nassert(u32(calls()) == 0)\n")
			} else {
				additions := 0
				if fail == 0 {
					additions = 1
				}
				fmt.Fprintf(&source, "assert(out[0] == u32(%d))\nassert(out[1] == u32(%d) && out[2] == 0)\n", want, additions)
				source.WriteString("assert(u32(calls()) == 6)\n")
			}
			source.WriteString("assert(u32(outstanding()) == 0 && u32(bad()) == 0)\n}\n")
		}
	}
	// Boundary counts, including the last arithmetically valid request. The
	// latter reaches the refusing allocator; the others must not reach it.
	for _, field := range []int{1, 5, 6} {
		for _, count := range []uint32{1073741822, 1073741823, 1 << 30, 0xfffffffe, 0xffffffff} {
			f, r := append([]uint32(nil), base.formula...), append([]uint32(nil), base.record...)
			r[field] = count
			if field == 1 {
				f[field] = count
			}
			source.WriteString("true ? {\n" + lratEntryWords("f", f) + lratEntryWords("r", r))
			source.WriteString("reset(c.UInt32(0))\nout: [3]u32\ns: u32 = lrat_check_record(view(&f), view(&r), span(&out))\nassert(s == LRAT_CAPACITY && out[0] == s && out[1] == 0 && out[2] == 0)\n")
			wantCalls := 0
			if count == 1073741822 {
				wantCalls = 6
			}
			fmt.Fprintf(&source, "assert(u32(calls()) == u32(%d))\nassert(u32(outstanding()) == 0 && u32(bad()) == 0)\n}\n", wantCalls)
		}
	}
	source.WriteString("0\n}\n")
	lratEntryRun(t, lratEntryBinary(t, source.String()), nil)
}

func TestOakLRATRawStreamEntry(t *testing.T) {
	source := lratAllocationExterns + oakLRATSource +
		lratSourceRegion(t, oakCertifySource, "lrat_check_record:", "// write_words_file") +
		lratSourceRegion(t, oakDriverHelpersSource, "copy_chunk:", "solve_one:") +
		lratSourceRegion(t, oakSolverDriverSource, "lrat_fill:", "// lrat_main reads") +
		lratSourceRegion(t, oakSolverDriverSource, "lrat_main:", "stream_main:") + `
CHUNK: u32 = 16384
c_read: (fd: c.Int, buf: c.Ptr, n: c.Size): c.UInt64 = c.extern("read")
putchar: (ch: c.Int): c.Int = c.extern("putchar")
write_byte: (ch: u8): () { ignored: c.Int = putchar(c.Int(i32(ch))) }
write_u32: (value: u32): () {
  digits: [10]u8
  n: u32 = value
  at: u32 = 10
  at = at - 1
  digits[at] = u8_trunc_u32(u32(48) + n % u32(10))
  n = n / 10
  while n > 0 {
    at = at - 1
    digits[at] = u8_trunc_u32(u32(48) + n % u32(10))
    n = n / 10
  }
  while at < 10 {
    write_byte(digits[at])
    at = at + 1
  }
}
main: (): i32 {
  // Read the failure index with the same unbuffered ABI as the driver.
  prefix: c.UInt8 = c.UInt8(0)
  got: u64 = u64(c_read(c.Int(0), c.out(prefix), c.Size(1)))
  assert(got == 1)
  reset(c.UInt32(u32(u8(prefix))))
  result: i32 = lrat_main()
  assert(u32(outstanding()) == 0 && u32(bad()) == 0)
  result
}
`
	bin := lratEntryBinary(t, source)
	encode := func(words []uint32) []byte {
		b := make([]byte, 4*len(words))
		for i, w := range words {
			binary.LittleEndian.PutUint32(b[4*i:], w)
		}
		return b
	}
	valid := formulaBindingCases(t)[0].record
	data := encode(valid)
	check := func(name string, fail byte, data []byte, status, additions int) {
		t.Run(name, func(t *testing.T) {
			got := lratEntryRun(t, bin, append([]byte{fail}, data...))
			if want := fmt.Sprintf("lrat %d %d 0\n", status, additions); got != want {
				t.Fatalf("got %q, want %q", got, want)
			}
		})
	}
	check("valid", 0, data, 0, 1)
	for fail := byte(1); fail <= 9; fail++ {
		check(fmt.Sprintf("allocation failure %d", fail), fail, data, 7, 0)
	}
	for n := 0; n < len(data); n++ {
		check(fmt.Sprintf("truncated byte %d", n), 0, data[:n], 1, 0)
	}
	for n := 1; n <= 5; n++ {
		check(fmt.Sprintf("trailing bytes %d", n), 0, append(append([]byte(nil), data...), make([]byte, n)...), 1, 0)
	}
	for _, field := range []int{1, 2, 3, 4, 5, 6} {
		for _, count := range []uint32{1073741823, 1 << 30, 0xfffffff8, 0xffffffff} {
			words := append([]uint32(nil), valid...)
			words[field] = count
			check(fmt.Sprintf("overflow %d/%x", field, count), 0, encode(words), 7, 0)
		}
	}
	empty, err := prove.EncodeLRATWords("p cnf 0 1\n0\n", "")
	if err != nil {
		t.Fatal(err)
	}
	check("zero variables initial empty", 0, encode(empty), 0, 0)
	check("zero body no empty", 0, encode([]uint32{prove.LRATMagic, 0, 0, 0, 0, 0, 0, 0}), 6, 0)
}
