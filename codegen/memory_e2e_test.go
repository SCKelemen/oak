package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func TestAtomicSourceLowersWithoutHeapOrRuntimeOrderDispatch(t *testing.T) {
	input := `
package main
counter: Atomic[u64]

fn ordered() -> u64
  atomic_store_release(counter, u64(1))
  atomic_fence_acq_rel()
  atomic_fetch_add_seq_cst(counter, u64(1))

fn bump() -> u64
  atomic_fetch_add_relaxed(counter, u64(1))

fn read() -> u64
  atomic_load_acquire(counter)
`
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	tc := typechecker.New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("type errors: %v", errs)
	}
	cg := New("main", tc)
	generated, err := cg.Generate(program, tc)
	if err != nil {
		t.Fatalf("code generation: %v", err)
	}

	for _, required := range []string{
		"#include <stdatomic.h>",
		"static _Atomic(u64) counter = 0;",
		"atomic_store_explicit(&(counter)",
		"memory_order_release",
		"atomic_thread_fence(memory_order_acq_rel)",
		"atomic_fetch_add_explicit(&(counter)",
		"memory_order_relaxed",
		"atomic_load_explicit(&(counter), memory_order_acquire)",
	} {
		if !strings.Contains(generated, required) {
			t.Fatalf("generated C missing %q:\n%s", required, generated)
		}
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free(", "switch (__oak_atomic_order"} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("atomic lowering introduced hidden allocation/runtime dispatch %q", forbidden)
		}
	}
}

func TestAtomicGeneratedCIsCorrectUnderContention(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("cc is required for native atomic execution test")
	}
	input := `
package main
counter: Atomic[u64]

fn ordered() -> u64
  atomic_store_release(counter, u64(1))
  atomic_fence_acq_rel()
  atomic_fetch_add_seq_cst(counter, u64(1))

fn bump() -> u64
  atomic_fetch_add_relaxed(counter, u64(1))

fn read() -> u64
  atomic_load_acquire(counter)
`
	p := parser.New(scanner.New(input))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	tc := typechecker.New(object.NewEnvironment())
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("type errors: %v", errs)
	}
	cg := New("main", tc)
	generated, err := cg.Generate(program, tc)
	if err != nil {
		t.Fatalf("code generation: %v", err)
	}

	harness := `
#include <pthread.h>
#define OAK_TEST_THREADS 4
#define OAK_TEST_ITERS 25000
static void* oak_atomic_runner(void* ignored) {
  (void)ignored;
  for (int i = 0; i < OAK_TEST_ITERS; ++i) {
    (void)oak_bump();
  }
  return NULL;
}
int main(void) {
  if (oak_ordered() != 1) return 10;
  pthread_t threads[OAK_TEST_THREADS];
  for (int i = 0; i < OAK_TEST_THREADS; ++i) {
    if (pthread_create(&threads[i], NULL, oak_atomic_runner, NULL) != 0) return 20;
  }
  for (int i = 0; i < OAK_TEST_THREADS; ++i) {
    if (pthread_join(threads[i], NULL) != 0) return 30;
  }
  const u64 expected = 2 + (u64)OAK_TEST_THREADS * (u64)OAK_TEST_ITERS;
  return oak_read() == expected ? 0 : 40;
}
`
	dir := t.TempDir()
	cPath := filepath.Join(dir, "atomic_e2e.c")
	binPath := filepath.Join(dir, "atomic_e2e")
	if err := os.WriteFile(cPath, []byte(generated+harness), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(cc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-pthread", cPath, "-o", binPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("compile generated C: %v\n%s\n--- C ---\n%s", err, output, generated+harness)
	}
	if output, err := exec.Command(binPath).CombinedOutput(); err != nil {
		t.Fatalf("native atomic program failed: %v\n%s", err, output)
	}
}
