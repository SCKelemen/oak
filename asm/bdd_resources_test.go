package asm

import (
	"math"
	"runtime"
	"sync/atomic"
	"testing"
	"time"
)

func smallBDDFunctions(b *bdd, variables int) []int {
	functions := make([]int, 1<<(1<<variables))
	for truth := range functions {
		var build func(int, int) int
		build = func(variable, prefix int) int {
			if variable == variables {
				return truth >> prefix & 1
			}
			return b.mk(variable, build(variable+1, prefix), build(variable+1, prefix|1<<variable))
		}
		functions[truth] = build(0, 0)
	}
	return functions
}

func TestBDDBoundedMemoRecomputesCanonicalResults(t *testing.T) {
	b := newBDD(1000)
	functions := smallBDDFunctions(b, 3)
	nodes := len(b.nodes)
	// A tiny cache forces repeated eviction within recursive operations.
	b.memo = newOpTable(32)
	b.memo.maxSlots = 32
	b.budget = nodes // all results already exist; no new node is permitted
	for a, x := range functions {
		for c, y := range functions {
			for _, tc := range []struct{ op, truth int }{{opAnd, a & c}, {opOr, a | c}, {opXor, a ^ c}} {
				if got := b.apply(tc.op, x, y); got != functions[tc.truth] {
					t.Fatalf("binary result changed after eviction: op=%d a=%d b=%d", tc.op, a, c)
				}
			}
			z := (a*31 + c*17) & 255
			if got := b.ite(x, y, functions[z]); got != functions[(a&c)|((^a)&z&255)] {
				t.Fatal("ITE result changed after eviction")
			}
		}
	}
	if b.exceeded || len(b.nodes) != nodes || b.unique.count != nodes-1 {
		t.Fatal("cache eviction changed canonical storage or exhausted existing-node operations")
	}
	if len(b.memo.entries) != 32 || b.memo.count > 16 || b.memo.resets == 0 {
		t.Fatalf("unbounded cache: slots=%d count=%d resets=%d", len(b.memo.entries), b.memo.count, b.memo.resets)
	}
}

func TestBDDMemoBoundAndCancellation(t *testing.T) {
	memo := newOpTable(8)
	memo.maxSlots = 8
	never := func() bool { return false }
	for i := int32(0); i < 10000; i++ {
		if !memo.insert(opXor, i, i+1, i, never) {
			t.Fatal("cache insertion unexpectedly exhausted")
		}
		if value, ok := memo.lookup(opXor, i, i+1); !ok || value != i {
			t.Fatal("cache lost newly inserted exact result")
		}
		if len(memo.entries) != 8 || memo.count > 4 {
			t.Fatal("memo exceeded bounded capacity")
		}
	}
	if memo.resets == 0 {
		t.Fatal("test never evicted")
	}
	before, count, resets := memo.entries[0], memo.count, memo.resets
	if memo.insert(opXor, 10001, 10002, 10001, func() bool { return true }) {
		t.Fatal("cancelled insert succeeded")
	}
	if before != memo.entries[0] || count != memo.count || resets != memo.resets {
		t.Fatal("cancelled insert mutated cache")
	}
	b := newBDD(100)
	if len(b.unique.entries) != 0 || len(b.memo.entries) != 0 {
		t.Fatal("queued candidate eagerly allocated tables")
	}
}

func TestBDDOrderEstimateAndOversize(t *testing.T) {
	base, high := bddOrderEstimate(2000000), bddOrderEstimate(16000000)
	if base == 0 || 5*base > bddOrderEstimateLimit || 2*high <= bddOrderEstimateLimit || high > bddOrderEstimateLimit {
		t.Fatalf("unexpected default admission: base=%d high=%d limit=%d", base, high, bddOrderEstimateLimit)
	}
	for _, budget := range []int{int(^uint(0) >> 1)} {
		if bddOrderEstimate(budget) != math.MaxUint64 {
			t.Fatal("oversized arithmetic did not saturate")
		}
	}
	bl := newBlaster(nil, nil).withBudget(16000000)
	pool := newBDDOrderAdmission(func() uint64 { return high - 1 })
	if _, decided := raceBDDOrdersAdmitted([]*blaster{bl}, func(*blaster) (int, bool) { t.Error("oversized order executed"); return 1, false }, pool); decided {
		t.Fatal("resource exhaustion became proof")
	}
	if !bl.bdd.memoryExhausted || bl.bdd.budget != 16000000 || bddExhaustionReason([]*blaster{bl}) != "memory admission allowance" {
		t.Fatal("memory exhaustion cause/allowance lost")
	}
}

func TestBDDOrderAdmissionPreservesEveryAllowance(t *testing.T) {
	const count = 5
	blasters := make([]*blaster, count)
	for i := range blasters {
		blasters[i] = newBlaster(nil, nil).withBudget(1234)
	}
	reservation := bddOrderEstimate(1234)
	pool := newBDDOrderAdmission(func() uint64 { return reservation })
	var active atomic.Int32
	seen := make(chan *blaster, count)
	_, decided := raceBDDOrdersAdmitted(blasters, func(bl *blaster) (int, bool) {
		if active.Add(1) != 1 {
			t.Error("single-order capacity was exceeded")
		}
		if bl.bdd.budget != 1234 {
			t.Error("node allowance changed")
		}
		seen <- bl
		active.Add(-1)
		return 0, true
	}, pool)
	if decided {
		t.Fatal("all exhausted attempts became a proof")
	}
	for _, want := range blasters {
		if got := <-seen; got != want {
			t.Fatal("queued candidate order was dropped or reordered")
		}
		if want.bdd.nodes != nil || want.bdd.unique.entries != nil || want.bdd.memo.entries != nil || want.memo != nil {
			t.Fatal("completed attempt retained its store")
		}
	}
	if pool.used != 0 || len(pool.queue) != 0 {
		t.Fatal("admission leaked a reservation or waiter")
	}
}

func TestBDDOrderAdmissionCancellationAndNestedDiagnostic(t *testing.T) {
	pool := newBDDOrderAdmission(func() uint64 { return 10 })
	var stop atomic.Bool
	if !pool.acquire(10, &stop) {
		t.Fatal("initial reservation denied")
	}
	if pool.tryAcquire(1) {
		t.Fatal("nested diagnostic exceeded capacity instead of failing closed")
	}
	ticket := pool.enqueue(1)[0]
	done := make(chan bool, 1)
	go func() { done <- pool.acquireQueued(ticket, 1, &stop) }()
	stop.Store(true)
	pool.wake()
	select {
	case admitted := <-done:
		if admitted {
			t.Fatal("cancelled waiter was admitted")
		}
	case <-time.After(time.Second):
		t.Fatal("cancelled waiter did not wake")
	}
	pool.release(10)
	if pool.used != 0 || len(pool.queue) != 0 {
		t.Fatal("cancelled waiter leaked state")
	}
}

func TestBDDOrderReservationCoversCleanup(t *testing.T) {
	blasters := []*blaster{newBlaster(nil, nil), newBlaster(nil, nil)}
	reservation := bddOrderEstimate(blastNodeBudget)
	pool := newBDDOrderAdmission(func() uint64 { return reservation })
	cleaning, release, second, done := make(chan struct{}), make(chan struct{}), make(chan struct{}), make(chan struct{})
	var cleanups atomic.Int32
	pool.cleanup = func(uint64) {
		if cleanups.Add(1) == 1 {
			close(cleaning)
			<-release
		}
	}
	go func() {
		raceBDDOrdersAdmitted(blasters, func(bl *blaster) (int, bool) {
			if bl == blasters[1] {
				close(second)
			}
			return 0, true
		}, pool)
		close(done)
	}()
	<-cleaning
	if blasters[0].bdd.nodes != nil || blasters[0].bdd.unique.entries != nil {
		t.Fatal("cleanup ran before stores became unreachable")
	}
	select {
	case <-second:
		close(release)
		t.Fatal("next order overlapped unreclaimed storage")
	case <-time.After(10 * time.Millisecond):
	}
	close(release)
	select {
	case <-done:
	case <-time.After(time.Second):
		t.Fatal("queued order did not run after cleanup")
	}
	if cleanups.Load() != 2 {
		t.Fatal("not every admitted order was cleaned")
	}
}

func TestBDDAdmissionSamplesOnlyBetweenActiveGroups(t *testing.T) {
	var samples atomic.Int32
	pool := newBDDOrderAdmission(func() uint64 { samples.Add(1); return 10 })
	var stop atomic.Bool
	if !pool.acquire(5, &stop) || !pool.acquire(5, &stop) {
		t.Fatal("valid reservations denied")
	}
	if samples.Load() != 1 {
		t.Fatal("live reservations were counted again through availability")
	}
	pool.release(5)
	pool.release(5)
	if !pool.acquire(10, &stop) || samples.Load() != 2 {
		t.Fatal("idle capacity was not refreshed")
	}
	pool.release(10)
}

func BenchmarkBDDOperationMemo(b *testing.B) {
	for _, bounded := range []bool{false, true} {
		name := "growing"
		if bounded {
			name = "bounded"
		}
		b.Run(name, func(b *testing.B) {
			engine := newBDD(40000)
			functions := smallBDDFunctions(engine, 4)
			engine.memo = newOpTable(1 << 16)
			if bounded {
				engine.memo.maxSlots = 1 << 16
			} else {
				engine.memo.maxSlots = 1 << 30
			}
			b.ResetTimer()
			for iteration := 0; iteration < b.N; iteration++ {
				seed := uint32(1)
				for i := 0; i < 65536; i++ {
					seed = seed*1664525 + 1013904223
					x := uint16(seed >> 8)
					seed = seed*1664525 + 1013904223
					y := uint16(seed >> 8)
					if got := engine.apply(opXor, functions[x], functions[y]); got != functions[x^y] {
						b.Fatal("recomputation changed result")
					}
				}
			}
			b.StopTimer()
			b.ReportMetric(float64(len(engine.memo.entries)*16), "memo_bytes")
			b.ReportMetric(float64(engine.memo.resets), "evictions")
			b.ReportMetric(float64(len(engine.nodes)), "nodes")
			runtime.KeepAlive(engine)
		})
	}
}

func TestBDDCgroupMembershipAndAncestorLimits(t *testing.T) {
	for _, tc := range []struct {
		name, membership, mounts string
		want                     []string
	}{
		{"v2 nested", "0::/team/job\n", "1 0 0:1 / /sys/fs/cgroup rw - cgroup2 cgroup rw\n", []string{"/sys/fs/cgroup/team/job/memory.max", "/sys/fs/cgroup/team/memory.max", "/sys/fs/cgroup/memory.max"}},
		{"v1 root", "7:cpu,memory:/tenant/leaf\n", "1 0 0:1 /tenant /sys/fs/cgroup/memory rw - cgroup cgroup rw,memory\n", []string{"/sys/fs/cgroup/memory/leaf/memory.limit_in_bytes", "/sys/fs/cgroup/memory/memory.limit_in_bytes"}},
		{"namespace root", "0::/\n", "1 0 0:1 /docker/123 /sys/fs/cgroup rw - cgroup2 cgroup rw\n", []string{"/sys/fs/cgroup/memory.max"}},
		{"escaped mount", "0::/leaf\n", "1 0 0:1 / /group\\040space rw - cgroup2 cgroup rw\n", []string{"/group space/leaf/memory.max", "/group space/memory.max"}},
		{"wrong controller", "2:cpu:/team\n", "1 0 0:1 / /sys/fs/cgroup rw - cgroup cgroup rw,cpu\n", nil},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got := bddCgroupMemoryPairs(tc.membership, tc.mounts)
			if len(got) != len(tc.want) {
				t.Fatalf("resolved %v; want %v", got, tc.want)
			}
			for i, pair := range got {
				if pair[0] != tc.want[i] {
					t.Fatalf("resolved %v; want %v", got, tc.want)
				}
			}
		})
	}
}

func TestBDDTransientDenialRetriesRealProof(t *testing.T) {
	names, widths := []string{"x", "y", "z"}, map[string]int{"x": 4, "y": 4, "z": 4}
	x, y, z := paramTerm("x", 4), paramTerm("y", 4), paramTerm("z", 4)
	left := binaryTerm("and", x, binaryTerm("or", y, z))
	right := binaryTerm("or", binaryTerm("and", x, y), binaryTerm("and", x, z))
	attempt := func(capacity uint64) (verdict Verdict) {
		defer trackBDDResourceExhaustion(&verdict)()
		bl := newBlaster(names, widths)
		proof, decided := raceBDDOrdersAdmitted([]*blaster{bl}, func(bl *blaster) (Verdict, bool) {
			return blastEqual(bl, &Function{Name: "retry"}, names, left, right, nil, 4, "")
		}, newBDDOrderAdmission(func() uint64 { return capacity }))
		if decided {
			return proof
		}
		return Verdict{Kind: VerdictWitnessed, Message: bddExhaustionReason([]*blaster{bl})}
	}
	denied := attempt(0)
	if denied.Kind != VerdictWitnessed || !denied.TransientResourceExhausted {
		t.Fatalf("denial lost transient status: %+v", denied)
	}
	proved := attempt(bddOrderEstimate(blastNodeBudget))
	if proved.Kind != VerdictProven || proved.TransientResourceExhausted {
		t.Fatalf("recovered memory did not permit actual proof: %+v", proved)
	}
	for _, kind := range []VerdictKind{VerdictTrusted, VerdictWitnessed, VerdictProven, VerdictMismatch} {
		verdict := Verdict{Kind: kind}
		finish := trackBDDResourceExhaustion(&verdict)
		bddAdmissionDenials.Add(1)
		finish()
		want := kind == VerdictTrusted || kind == VerdictWitnessed
		if verdict.TransientResourceExhausted != want {
			t.Fatalf("resource status for %v = %v", kind, verdict.TransientResourceExhausted)
		}
	}
}

func TestBDDBoundedMemoProofRefutationAndExhaustion(t *testing.T) {
	names, widths := []string{"x", "y", "z"}, map[string]int{"x": 4, "y": 4, "z": 4}
	x, y, z := paramTerm("x", 4), paramTerm("y", 4), paramTerm("z", 4)
	left := binaryTerm("and", x, binaryTerm("or", y, z))
	right := binaryTerm("or", binaryTerm("and", x, y), binaryTerm("and", x, z))
	for _, tc := range []struct {
		name string
		a, b *term
		want VerdictKind
	}{
		{"proof", left, right, VerdictProven},
		{"refutation", binaryTerm("xor", x, y), binaryTerm("or", x, y), VerdictMismatch},
	} {
		for _, budget := range []int{1, 1000} {
			bl := newBlaster(names, widths).withBudget(budget)
			bl.bdd.memo = newOpTable(8)
			bl.bdd.memo.maxSlots = 8
			verdict, exhausted := blastEqual(bl, &Function{Name: tc.name}, names, tc.a, tc.b, nil, 4, "")
			if budget == 1 {
				if !exhausted {
					t.Fatal("node exhaustion became a verdict")
				}
				continue
			}
			if exhausted || verdict.Kind != tc.want || len(bl.bdd.memo.entries) > 8 || bl.bdd.memo.resets == 0 {
				t.Fatalf("%s after eviction: verdict=%v exhausted=%v cache=%d resets=%d", tc.name, verdict.Kind, exhausted, len(bl.bdd.memo.entries), bl.bdd.memo.resets)
			}
		}
	}
}

func TestBDDTransientStatusSurvivesNestedBooleanHelpers(t *testing.T) {
	// Loop/split helpers return only booleans; an outer Verify-style scope
	// must preserve a real nested admission denial for Trusted as well as
	// Witnessed outcomes (including an undecided abstract-call fallback).
	for _, kind := range []VerdictKind{VerdictTrusted, VerdictWitnessed} {
		outer := func() (verdict Verdict) {
			defer trackBDDResourceExhaustion(&verdict)()
			inner := func() bool {
				bl := newBlaster(nil, nil)
				_, decided := raceBDDOrdersAdmitted([]*blaster{bl}, func(*blaster) (bool, bool) { t.Fatal("denied child ran"); return true, false }, newBDDOrderAdmission(func() uint64 { return 0 }))
				return decided
			}
			if inner() {
				t.Fatal("nested denial became a decision")
			}
			return Verdict{Kind: kind, Message: "undecided nested/abstract obligation"}
		}
		if verdict := outer(); !verdict.TransientResourceExhausted {
			t.Fatalf("nested resource cause lost for %v", kind)
		}
	}
	before := bddAdmissionDenials.Load()
	probe := newBlaster(nil, nil).withBudget(int(^uint(0) >> 1))
	if finish, admitted := admitBDDStandalone(probe, true); admitted {
		finish()
		t.Fatal("oversized diagnostic admitted")
	}
	if bddAdmissionDenials.Load() != before {
		t.Fatal("optional diagnostic refusal tainted proof cache status")
	}
	bl := newBlaster(nil, nil)
	pool := newBDDOrderAdmission(func() uint64 { return bddOrderEstimate(blastNodeBudget) })
	raceBDDOrdersAdmitted([]*blaster{bl}, func(bl *blaster) (bool, bool) { bl.bdd.stop.Store(true); return false, true }, pool)
	if bddAdmissionDenials.Load() != before {
		t.Fatal("ordinary cancellation counted as memory denial")
	}
}

func TestBDDLogicalBudgetBoundariesStayDeterministic(t *testing.T) {
	for _, budget := range []int{-1, 0, 1, 2} {
		if budget <= 1 && bddOrderEstimate(budget) != bddOrderEstimate(1) {
			t.Fatalf("logical budget %d became oversized memory request", budget)
		}
		for _, constant := range []bool{false, true} {
			attempt := func() (verdict Verdict) {
				defer trackBDDResourceExhaustion(&verdict)()
				bl := newBlaster([]string{"x"}, map[string]int{"x": 1}).withBudget(budget)
				term := paramTerm("x", 1)
				if constant {
					term = constTerm(1, 1)
				}
				result, decided := raceBDDOrdersAdmitted([]*blaster{bl}, func(bl *blaster) (Verdict, bool) {
					return blastEqual(bl, &Function{Name: "logical_boundary"}, []string{"x"}, term, term, nil, 1, "")
				}, newBDDOrderAdmission(func() uint64 { return bddOrderEstimate(budget) }))
				if bl.bdd.budget != budget || bl.bdd.memoryExhausted {
					t.Fatal("logical allowance/cause changed")
				}
				if decided {
					return result
				}
				return Verdict{Kind: VerdictWitnessed, Message: bddExhaustionReason([]*blaster{bl})}
			}
			verdict := attempt()
			want := VerdictWitnessed
			if constant || budget >= 2 {
				want = VerdictProven
			}
			if verdict.Kind != want || verdict.TransientResourceExhausted {
				t.Fatalf("budget=%d constant=%v: %+v", budget, constant, verdict)
			}
		}
	}
}
