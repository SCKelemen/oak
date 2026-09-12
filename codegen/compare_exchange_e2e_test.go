package codegen

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const compareExchangeSource = `
package main
counter: Atomic[u64]

fn cas(expected: u64, desired: u64) -> u64
  atomic_compare_exchange_acq_rel_acquire(counter, expected, desired)

fn cas_relaxed(expected: u64, desired: u64) -> u64
  atomic_compare_exchange_relaxed_relaxed(counter, expected, desired)

fn read() -> u64
  atomic_load_acquire(counter)
`

func TestCompareExchangeLowersToStrongC11WithoutHeapOrOrderDispatch(t *testing.T) {
	generated := generateSourceC(t, compareExchangeSource)
	for _, required := range []string{
		"atomic_compare_exchange_strong_explicit",
		"OAK_ORDER_CAS_ACQ_REL, memory_order_acquire",
		"memory_order_relaxed, memory_order_relaxed",
		"_Generic((cell)",
		"__oak_cas_acq_rel_acquire(&(counter)",
	} {
		if !strings.Contains(generated, required) {
			t.Fatalf("generated CAS C missing %q:\n%s", required, generated)
		}
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "free(", "switch (__oak_cas", "memory_order success", "memory_order failure"} {
		if strings.Contains(generated, forbidden) {
			t.Fatalf("CAS lowering introduced hidden cost/runtime order dispatch %q", forbidden)
		}
	}
}

func TestCompareExchangeGeneratedCUnderContention(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("cc is required for native compare-exchange execution test")
	}
	generated := generateSourceC(t, compareExchangeSource)
	harness := `
#include <pthread.h>
#include <stdio.h>
#define OAK_THREADS 4
#define OAK_ITERS 25000
static _Atomic(u64) attempts = 0;
static _Atomic(u64) retries = 0;

static void* worker(void* ignored) {
  (void)ignored;
  for (int i = 0; i < OAK_ITERS; ++i) {
    u64 expected = oak_read();
    for (;;) {
      atomic_fetch_add_explicit(&attempts, 1, memory_order_relaxed);
      u64 observed = oak_cas(expected, expected + 1);
      if (observed == expected) break;
      atomic_fetch_add_explicit(&retries, 1, memory_order_relaxed);
      expected = observed;
    }
  }
  return NULL;
}

int main(void) {
  if (oak_cas_relaxed(7, 9) != 0) return 10;
  if (oak_read() != 0) return 11;
  if (oak_cas_relaxed(0, 1) != 0) return 12;
  if (oak_read() != 1) return 13;

  pthread_t threads[OAK_THREADS];
  for (int i = 0; i < OAK_THREADS; ++i)
    if (pthread_create(&threads[i], NULL, worker, NULL) != 0) return 20;
  for (int i = 0; i < OAK_THREADS; ++i)
    if (pthread_join(threads[i], NULL) != 0) return 30;

  const u64 expected_final = 1 + (u64)OAK_THREADS * (u64)OAK_ITERS;
  const u64 final = oak_read();
  const u64 a = atomic_load_explicit(&attempts, memory_order_relaxed);
  const u64 r = atomic_load_explicit(&retries, memory_order_relaxed);
  if (final != expected_final) return 40;
  if (a < (u64)OAK_THREADS * (u64)OAK_ITERS) return 41;
  if (r > a) return 42;
  printf("attempts=%llu retries=%llu final=%llu\n",
         (unsigned long long)a, (unsigned long long)r, (unsigned long long)final);
  return 0;
}
`
	dir := t.TempDir()
	cPath := filepath.Join(dir, "cas_e2e.c")
	binPath := filepath.Join(dir, "cas_e2e")
	if err := os.WriteFile(cPath, []byte(generated+harness), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(cc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-pthread", cPath, "-o", binPath)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("compile generated CAS C: %v\n%s\n--- C ---\n%s", err, output, generated+harness)
	}
	output, err := exec.Command(binPath).CombinedOutput()
	if err != nil {
		t.Fatalf("native CAS program failed: %v\n%s", err, output)
	}
	if !strings.Contains(string(output), "attempts=") || !strings.Contains(string(output), "retries=") {
		t.Fatalf("CAS contention instrumentation missing: %s", output)
	}
}
