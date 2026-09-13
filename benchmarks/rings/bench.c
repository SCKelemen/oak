/* The rings benchmark driver (benchmarks/rings/README.md): appended to the
   C the Oak compiler emits for benchmarks/rings/oak, it owns every ring's
   storage, runs the producers and consumers on pthreads, and prints one
   JSON line per ring with the wall time per item. Checksums are verified
   before a timing counts. */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#ifdef YIELD
#include <sched.h>
#endif

#ifndef ITEMS
#define ITEMS 2000000u
#endif
#ifndef P
#define P 4
#endif
#ifdef YIELD
#define POLICY "yield"
#else
#define POLICY "spin"
#endif

static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static oak_rings__SpscCursor spsc_state[1];
static u32 spsc_data[1024];
#define SPSC (oak_span_oak_rings_SpscCursor){ spsc_state, 1 }, (oak_span_u32){ spsc_data, 1024 }
#ifdef YIELD
static void *spsc_prod(void *a) {
  u32 spins = 0;
  for (u32 i = 1; i <= ITEMS; i++) while (!oak_rings__spsc_upush_u32(SPSC, i)) { spins++; sched_yield(); }
  *(u32 *)a = spins; return NULL;
}
#else
static void *spsc_prod(void *a) { *(u32 *)a = oak_spsc_produce(SPSC, ITEMS); return NULL; }
#endif
static void *spsc_cons(void *a) { *(u64 *)a = oak_spsc_consume(SPSC, ITEMS); return NULL; }

static oak_rings__MpscCursor mpsc_state[1];
static oak_rings__SeqCell mpsc_seqs[1024];
static u32 mpsc_data[1024];
#define MPSC (oak_span_oak_rings_MpscCursor){ mpsc_state, 1 }, (oak_span_oak_rings_SeqCell){ mpsc_seqs, 1024 }, (oak_span_u32){ mpsc_data, 1024 }
#ifdef YIELD
/* The yield policy: the producer loop in C calls the ring's push and
   yields the core when the ring is full, instead of spinning on the slot
   the consumer is about to release. */
static void *mpsc_prod(void *a) {
  u32 spins = 0;
  for (u32 i = 1; i <= ITEMS / P; i++) while (!oak_rings__mpsc_upush_u32(MPSC, i)) { spins++; sched_yield(); }
  *(u32 *)a = spins; return NULL;
}
#else
static void *mpsc_prod(void *a) { *(u32 *)a = oak_mpsc_produce(MPSC, ITEMS / P); return NULL; }
#endif
static void *mpsc_cons(void *a) { *(u64 *)a = oak_mpsc_consume(MPSC, ITEMS); return NULL; }

static oak_rings__MpmcCursor mpmc_state[1];
static oak_rings__SeqCell mpmc_seqs[1024];
static u32 mpmc_data[1024];
#define MPMC (oak_span_oak_rings_MpmcCursor){ mpmc_state, 1 }, (oak_span_oak_rings_SeqCell){ mpmc_seqs, 1024 }, (oak_span_u32){ mpmc_data, 1024 }
#ifdef YIELD
static void *mpmc_prod(void *a) {
  u32 spins = 0;
  for (u32 i = 1; i <= ITEMS / P; i++) while (!oak_rings__mpmc_upush_u32(MPMC, i)) { spins++; sched_yield(); }
  *(u32 *)a = spins; return NULL;
}
#else
static void *mpmc_prod(void *a) { *(u32 *)a = oak_mpmc_produce(MPMC, ITEMS / P); return NULL; }
#endif
static void *mpmc_cons(void *a) { *(u64 *)a = oak_mpmc_consume(MPMC, ITEMS / P); return NULL; }

static oak_rings__IntrusiveCursor intr_state[1];
static oak_rings__IntrusiveNode intr_nodes[1 + ITEMS];
#define INTR (oak_span_oak_rings_IntrusiveCursor){ intr_state, 1 }, (oak_span_oak_rings_IntrusiveNode){ intr_nodes, 1 + ITEMS }
static void *intr_prod(void *a) { oak_intrusive_produce(INTR, (u32)(long)a * (ITEMS / P) + 1, ITEMS / P); return NULL; }
static void *intr_cons(void *a) { *(u64 *)a = oak_intrusive_consume(INTR, ITEMS); return NULL; }

static u64 expected_sum(void) { return (u64)ITEMS * ((u64)ITEMS + 1) / 2; }
/* MPSC/MPMC: P producers each push 1..ITEMS/P. */
static u64 expected_parts(void) { u64 n = ITEMS / P; return (u64)P * (n * (n + 1) / 2); }

static void report(const char *ring, const char *threads, double ns, u64 got, u64 want, u32 spins) {
  if (got != want) { fprintf(stderr, "%s: checksum %llu, want %llu\n", ring, (unsigned long long)got, (unsigned long long)want); exit(1); }
  printf("{\"ring\":\"%s\",\"threads\":\"%s\",\"policy\":\"%s\",\"items\":%u,\"ns_per_item\":%.3f,\"producer_spins\":%u}\n", ring, threads, POLICY, ITEMS, ns / ITEMS, spins);
}

int main(void) {
  pthread_t p, c, ps[P], cs[P];
  u64 sum = 0, sums[P];
  u32 spins = 0, spinsv[P];
  double t0;

  t0 = now_ns();
  pthread_create(&c, NULL, spsc_cons, &sum);
  pthread_create(&p, NULL, spsc_prod, &spins);
  pthread_join(p, NULL); pthread_join(c, NULL);
  report("spsc", "1 producer, 1 consumer", now_ns() - t0, sum, expected_sum(), spins);

  oak_mpsc_setup((oak_span_oak_rings_MpscCursor){ mpsc_state, 1 }, (oak_span_oak_rings_SeqCell){ mpsc_seqs, 1024 });
  sum = 0; t0 = now_ns();
  pthread_create(&c, NULL, mpsc_cons, &sum);
  for (long i = 0; i < P; i++) pthread_create(&ps[i], NULL, mpsc_prod, &spinsv[i]);
  for (int i = 0; i < P; i++) pthread_join(ps[i], NULL);
  pthread_join(c, NULL);
  spins = 0; for (int i = 0; i < P; i++) spins += spinsv[i];
  report("mpsc", "4 producers, 1 consumer", now_ns() - t0, sum, expected_parts(), spins);

  oak_mpmc_setup((oak_span_oak_rings_MpmcCursor){ mpmc_state, 1 }, (oak_span_oak_rings_SeqCell){ mpmc_seqs, 1024 });
  t0 = now_ns();
  for (long i = 0; i < P; i++) pthread_create(&cs[i], NULL, mpmc_cons, &sums[i]);
  for (long i = 0; i < P; i++) pthread_create(&ps[i], NULL, mpmc_prod, &spinsv[i]);
  for (int i = 0; i < P; i++) pthread_join(ps[i], NULL);
  sum = 0; for (int i = 0; i < P; i++) { pthread_join(cs[i], NULL); sum += sums[i]; }
  spins = 0; for (int i = 0; i < P; i++) spins += spinsv[i];
  report("mpmc", "4 producers, 4 consumers", now_ns() - t0, sum, expected_parts(), spins);

  oak_intrusive_setup(INTR);
  sum = 0; t0 = now_ns();
  pthread_create(&c, NULL, intr_cons, &sum);
  for (long i = 0; i < P; i++) pthread_create(&ps[i], NULL, intr_prod, (void *)i);
  for (int i = 0; i < P; i++) pthread_join(ps[i], NULL);
  pthread_join(c, NULL);
  report("intrusive", "4 producers, 1 consumer", now_ns() - t0, sum, expected_sum(), 0);
  return 0;
}
