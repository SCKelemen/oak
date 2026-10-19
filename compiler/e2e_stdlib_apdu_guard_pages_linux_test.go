//go:build linux

package compiler

import (
 "context"
 "bytes"
 "errors"
 "fmt"
 "os"
 "os/exec"
 "path/filepath"
 "strings"
 "syscall"
 "testing"
 "time"
)

// Fixed test-only capture. The test still refuses any overflow after joining.
type apduGuardCapture struct { data bytes.Buffer; overflow bool }
func (b *apduGuardCapture) Write(p []byte) (int,error) {
 n:=len(p); remain:=(32<<10)-b.data.Len()
 if len(p)>remain { b.overflow=true; p=p[:remain] }
 _,_ = b.data.Write(p); return n,nil
}

// This is runtime evidence for the portable C backend. It is not a proof of
// physical accesses and does not exercise native candidate selection.
func TestE2EStdlibCommandAPDUGuardPages(t *testing.T) {
 cc, err := exec.LookPath("cc")
 if err != nil { t.Fatal("guard-page coverage requires cc:", err) }
 cases := commandAPDUSmallFixtures()
 if len(cases) != 54 { t.Fatalf("fixture inventory: %d", len(cases)) }
 root := writeModule(t, map[string]string{
  "oak.mod": "module example.com/apdu-guard-pages\noak 0.1.0\n",
  "main.oak": "package main\nimport(\"smartcard/apdu\")\nimport(\"bytes\")\n" + apduAssertions + `
main: (): i32 {
  wire: [4]u8 = [4]u8{ u8(225), u8(242), u8(195), u8(212) }
  frame: []u8 = view(&wire)
  assert(expect_command(frame, u32(1), u32(4), u32(0), u32(0)))
  empty: []u8 = frame[u32(0):u32(0)]
  assert(expect_error(empty, u32(2)))
  42
}
`,
 })
 output, err := New().WithPackageDir(root).EmitC().Get()
 if err != nil { t.Fatal(err) }
 for _, forbidden := range []string{"OAK_UNSUPPORTED", "malloc(", "calloc(", "realloc("} {
  if strings.Contains(output, forbidden) { t.Fatalf("unexpected generated C: %s", forbidden) }
 }
 var harness strings.Builder
 harness.WriteString("#define _GNU_SOURCE\n#define main oak_guard_unused_main\n")
 harness.WriteString(output)
 harness.WriteString("\n#undef main\n#include <sys/mman.h>\n#include <sys/resource.h>\n#include <unistd.h>\n#include <stdio.h>\n#include <string.h>\n")
 for i, f := range cases {
  fmt.Fprintf(&harness, "static const unsigned char wire_%d[] = {", i)
  if len(f.wire)==0 { harness.WriteString("0") }
  for _, b := range f.wire { fmt.Fprintf(&harness, "%d,", b) }
  harness.WriteString("};\n")
 }
 harness.WriteString(`
static unsigned char *mapping(size_t *page) {
  long n = sysconf(_SC_PAGESIZE);
  if (n <= 0 || (size_t)n > ((size_t)-1)/3) return NULL;
  *page = (size_t)n;
  void *p = mmap(NULL, 3 * *page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) return NULL;
  if (mprotect((unsigned char *)p + *page, *page, PROT_READ | PROT_WRITE)) {
    munmap(p, 3 * *page); return NULL;
  }
  return p;
}
static int fixture(const unsigned char *wire, size_t n, u32 form, u32 at,
                   u32 count, u32 response, u32 error, int right) {
  size_t page; unsigned char *p = mapping(&page);
  if (!p) return 10;
  if (n > page) { munmap(p, 3*page); return 11; }
  // Empty right-aligned frame points into PROT_NONE: even a first-byte read fails.
  unsigned char *frame = right ? p + 2*page - n : p + page;
  if (n) memcpy(frame, wire, n);
  if (mprotect(p + page, page, PROT_READ)) { munmap(p, 3*page); return 12; }
  oak_view_u8 view = { frame, (u32)n };
  int ok = error ? oak_expect_error(view, error)
                 : oak_expect_command(view, form, at, count, response);
  // Read-only storage detects writes even when a write would restore old bytes.
  if (n && memcmp(frame, wire, n)) ok = 0;
  if (munmap(p, 3*page)) return 13;
  return ok ? 0 : 14;
}
static int probe(const char *kind) {
  size_t page; unsigned char *p = mapping(&page);
  if (!p) return 20;
  if (mprotect(p + page, page, PROT_READ)) return 21;
  if (!strcmp(kind,"left")) { volatile unsigned char x = p[page-1]; (void)x; }
  else if (!strcmp(kind,"right")) { volatile unsigned char x = p[2*page]; (void)x; }
  else if (!strcmp(kind,"write")) { *(volatile unsigned char *)(p+page) = 1; }
  else return 22;
  munmap(p,3*page);
  return 23; // A probe returning normally means the test arrangement is broken.
}
int main(int argc, char **argv) {
  struct rlimit no_core = { 0, 0 };
  if (setrlimit(RLIMIT_CORE, &no_core)) return 26;
  if (argc == 2) return probe(argv[1]);
  if (argc != 1) return 24;
  int code; unsigned passed = 0;
`)
 for i,f := range cases {
  fmt.Fprintf(&harness,"for (int side=0; side<2; ++side) { code=fixture(wire_%d,%d,%d,%d,%d,%d,%d,side); if(code) { fprintf(stderr,\"fixture %d side %%d code %%d\\n\",side,code); return code; } ++passed; }\n",i,len(f.wire),f.form,f.at,f.count,f.want,f.err,i)
 }
 harness.WriteString("if(passed != 108) return 25; puts(\"APDU guard pages: 108 passed\"); return 0; }\n")
 if harness.Len() > 4<<20 { t.Fatal("generated guard C exceeds 4 MiB") }
 dir:=t.TempDir(); source:=filepath.Join(dir,"guard.c")
 if err:=os.WriteFile(source,[]byte(harness.String()),0600);err!=nil {t.Fatal(err)}
 // One clock for two builds, two positive runs, and three sensitivity probes.
 ctx,cancel:=context.WithTimeout(context.Background(),90*time.Second);defer cancel()
 capture:=func(cmd *exec.Cmd)([]byte,error) {
  var output apduGuardCapture
  cmd.Stdout=&output; cmd.Stderr=&output; cmd.WaitDelay=2*time.Second
  err:=cmd.Run()
  if output.overflow { t.Fatal("guard-page command output exceeds 32 KiB") }
  return output.data.Bytes(),err
 }
 for _,opt:=range []string{"-O0","-O2"} {
  binary:=filepath.Join(dir,"guard"+opt)
  build:=exec.CommandContext(ctx,cc,"-std=c99",opt,"-o",binary,source)
  if out,err:=capture(build);err!=nil {t.Fatalf("%s build: %v\n%s",opt,err,out)}
  run:=exec.CommandContext(ctx,binary)
  if out,err:=capture(run);err!=nil || string(out)!="APDU guard pages: 108 passed\n" {t.Fatalf("%s execution: %v\n%s",opt,err,out)}
  if opt=="-O2" {
   for _,kind:=range []string{"left","right","write"} {
    run:=exec.CommandContext(ctx,binary,kind); out,err:=capture(run)
    var exit *exec.ExitError
    if ctx.Err()!=nil || !errors.As(err,&exit) {t.Fatalf("%s probe did not fault: %v %s",kind,err,out)}
    status,ok:=exit.Sys().(syscall.WaitStatus)
    if !ok || !status.Signaled() || (status.Signal()!=syscall.SIGSEGV && status.Signal()!=syscall.SIGBUS) {t.Fatalf("%s wrong fault: %v %s",kind,err,out)}
   }
  }
 }
}
