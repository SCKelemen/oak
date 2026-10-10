package asm

import (
	"fmt"
	"math"
	"os"
	"path"
	"runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"unsafe"
)

const (
	// This is an admission estimate, NOT a process RSS limit. The race
	// detector and Go runtime have storage beyond these owned BDD arrays.
	bddOrderEstimateLimit = uint64(2<<30) * bddRaceMemoryFactor
	bddHostHeadroom       = uint64(1 << 30)
	bddScavengeThreshold  = uint64(64 << 20)
)

// bddOrderEstimate allows the existing full logical node budget. Nodes may
// have 25% spare slice capacity, with the previous backing array still live
// during growth (2.5 * budget * sizeof(node)). The half-full unique table
// rounds up to a power of two and may overlap its half-sized predecessor.
// The capped memo has the same growth overlap. Auxiliary maps/stacks add an
// estimated 64 MiB; this is not a bound on arbitrary source terms or restrict
// walks. Uncollected older arrays and race metadata also require measurement.
func bddOrderEstimate(budget int) uint64 {
	if budget > 1<<30 {
		return math.MaxUint64 // cannot admit an oversized numeric allowance
	}
	// Recursive proof debits can leave zero or negative logical budgets.
	// They still admit terminal-only work; attempting a new node exhausts
	// the unchanged logical budget. They are not oversized memory requests.
	nodes := uint64(max(budget, 1))
	uniqueSlots := uint64(1 << 16)
	for uniqueSlots < 2*nodes {
		uniqueSlots *= 2
	}
	estimate := (5*nodes*uint64(unsafe.Sizeof(bddNode{})) + 1) / 2
	estimate += uniqueSlots * uint64(unsafe.Sizeof(uniqueEntry{})) * 3 / 2
	estimate += uint64(opMemoMaxSlots) * uint64(unsafe.Sizeof(opEntry{})) * 3 / 2
	estimate += 64 << 20
	return estimate * bddRaceMemoryFactor
}

// bddAdmissionCapacity samples only at an idle-to-active transition. A fixed
// capacity is kept while reservations are live, so those same reservations
// are not subtracted a second time through a falling MemAvailable reading.
func bddAdmissionCapacity() uint64 {
	limit := bddOrderEstimateLimit
	if available, known := bddAvailableMemory(); known {
		if available <= bddHostHeadroom {
			return 0
		}
		limit = min(limit, available-bddHostHeadroom)
	}
	return limit
}

// Linux exposes both host and common cgroup limits. Other systems, or a
// missing/unreadable probe, retain the finite conservative estimate limit.
// These observations are admission hints, not promises of future free RAM.
func bddAvailableMemory() (uint64, bool) {
	var available uint64
	known := false
	if data, err := os.ReadFile("/proc/meminfo"); err == nil {
		for _, line := range strings.Split(string(data), "\n") {
			fields := strings.Fields(line)
			if len(fields) == 3 && fields[0] == "MemAvailable:" && fields[2] == "kB" {
				if n, err := strconv.ParseUint(fields[1], 10, 64); err == nil && n <= math.MaxUint64/1024 {
					available, known = n*1024, true
				}
			}
		}
	}
	pairs := [][2]string{
		{"/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory.current"},
		{"/sys/fs/cgroup/memory/memory.limit_in_bytes", "/sys/fs/cgroup/memory/memory.usage_in_bytes"},
	}
	membership, memberErr := os.ReadFile("/proc/self/cgroup")
	mounts, mountErr := os.ReadFile("/proc/self/mountinfo")
	if memberErr == nil && mountErr == nil {
		pairs = append(pairs, bddCgroupMemoryPairs(string(membership), string(mounts))...)
	}
	for _, files := range pairs {
		limit, errLimit := readBDDMemoryNumber(files[0])
		used, errUsed := readBDDMemoryNumber(files[1])
		if errLimit == nil && errUsed == nil {
			remaining := uint64(0)
			if used < limit {
				remaining = limit - used
			}
			if !known || remaining < available {
				available, known = remaining, true
			}
		}
	}
	return available, known
}

func readBDDMemoryNumber(path string) (uint64, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return 0, err
	}
	return strconv.ParseUint(strings.TrimSpace(string(data)), 10, 64)
}

// bddOrderAdmission is process-wide, FIFO weighted admission for top-level
// order races. Do not acquire it from newBDD: sequential split/probe code can
// own a parent diagram while creating a child. Production race callbacks
// (blastEqual/decideBlasted/impliesEqualUnder) never start another order race.
// Their callers recurse/split only after the previous race has joined and
// released its stores. Optional nested diagnostic stores use tryAcquire.
// The estimate covers admitted BDD work, not every compiler allocation.
type bddOrderAdmission struct {
	mu          sync.Mutex
	cond        *sync.Cond
	capacity    func() uint64
	limit, used uint64
	queue       []*bddAdmissionWaiter
	cleanup     func(uint64)
}

type bddAdmissionWaiter struct{ marker byte }

func newBDDOrderAdmission(capacity func() uint64) *bddOrderAdmission {
	p := &bddOrderAdmission{capacity: capacity, cleanup: scavengeBDDStores}
	p.cond = sync.NewCond(&p.mu)
	return p
}

var processBDDOrders = newBDDOrderAdmission(bddAdmissionCapacity)

func (p *bddOrderAdmission) enqueue(count int) []*bddAdmissionWaiter {
	p.mu.Lock()
	defer p.mu.Unlock()
	waiters := make([]*bddAdmissionWaiter, count)
	for i := range waiters {
		waiters[i] = &bddAdmissionWaiter{}
	}
	p.queue = append(p.queue, waiters...)
	return waiters
}

func (p *bddOrderAdmission) acquire(bytes uint64, stop *atomic.Bool) bool {
	return p.acquireQueued(p.enqueue(1)[0], bytes, stop)
}

func (p *bddOrderAdmission) acquireQueued(waiter *bddAdmissionWaiter, bytes uint64, stop *atomic.Bool) bool {
	p.mu.Lock()
	defer p.mu.Unlock()
	remove := func() {
		for i, w := range p.queue {
			if w == waiter {
				p.queue = append(p.queue[:i], p.queue[i+1:]...)
				break
			}
		}
		p.cond.Broadcast()
	}
	for {
		if stop.Load() {
			remove()
			return false
		}
		if p.used == 0 {
			p.limit = p.capacity()
		}
		if bytes > p.limit {
			// No unbudgeted exclusive exception, and no indefinite wait
			// for a request which cannot fit. This order is undecided.
			remove()
			return false
		}
		if p.queue[0] == waiter && bytes <= p.limit-p.used {
			p.used += bytes
			remove()
			return true
		}
		p.cond.Wait()
	}
}

func (p *bddOrderAdmission) release(bytes uint64) {
	p.mu.Lock()
	p.used -= bytes
	p.cond.Broadcast()
	p.mu.Unlock()
}

func (p *bddOrderAdmission) wake() {
	p.mu.Lock()
	p.cond.Broadcast()
	p.mu.Unlock()
}

// releaseBDDStores detaches the original blaster slice's references before
// GC, including the term cache and select abstractions. The logical budget
// stays available for diagnostics, but the consumed diagram is unusable.
func releaseBDDStores(bl *blaster) uint64 {
	b := bl.bdd
	bytes := uint64(cap(b.nodes))*uint64(unsafe.Sizeof(bddNode{})) +
		uint64(len(b.unique.entries))*uint64(unsafe.Sizeof(uniqueEntry{})) +
		uint64(len(b.memo.entries))*uint64(unsafe.Sizeof(opEntry{}))
	b.completedNodes = len(b.nodes)
	b.nodes, b.unique.entries, b.memo.entries = nil, nil, nil
	b.unique.count, b.memo.count = 0, 0
	b.exceeded = true
	bl.memo, bl.selects, bl.owners = nil, nil, nil
	bl.slotPlaces, bl.blockUsed = nil, nil
	return bytes
}

var bddScavengeMu sync.Mutex

func scavengeBDDStores(bytes uint64) {
	if bytes < bddScavengeThreshold {
		return
	}
	// No admission lock is held. The reservation remains live until after
	// GC/scavenging, preventing replacement orders from overlapping dead
	// but not yet collected large stores. This does not reclaim race shadow
	// memory or guarantee an OS RSS value.
	bddScavengeMu.Lock()
	debug.FreeOSMemory()
	bddScavengeMu.Unlock()
}

// tryAcquire is for optional diagnostic children. A child cannot wait for
// its parent's reservation. It runs with an additional reservation or reports
// diagnostic exhaustion without affecting the parent proof's result.
func (p *bddOrderAdmission) tryAcquire(bytes uint64) bool {
	p.mu.Lock()
	defer p.mu.Unlock()
	if p.used == 0 {
		p.limit = p.capacity()
	}
	if len(p.queue) != 0 || bytes > p.limit-p.used {
		return false
	}
	p.used += bytes
	return true
}

func admitBDDStandalone(bl *blaster, diagnostic bool) (finish func(), admitted bool) {
	reservation := bddOrderEstimate(bl.bdd.budget)
	var stop atomic.Bool
	if diagnostic {
		admitted = processBDDOrders.tryAcquire(reservation)
	} else {
		admitted = processBDDOrders.acquire(reservation, &stop)
	}
	if !admitted {
		bl.bdd.memoryExhausted, bl.bdd.exceeded = true, true
		if !diagnostic {
			bddAdmissionDenials.Add(1)
		}
		traceBDDResources("denied", bl, reservation)
		releaseBDDStores(bl)
		return nil, false
	}
	traceBDDResources("start", bl, reservation)
	return func() {
		traceBDDResources("finish", bl, reservation)
		scavengeBDDStores(releaseBDDStores(bl))
		processBDDOrders.release(reservation)
	}, true
}

func bddOrdersMemoryExhausted(blasters []*blaster) bool {
	for _, bl := range blasters {
		if bl.bdd.memoryExhausted {
			return true
		}
	}
	return false
}

func bddExhaustionReason(blasters []*blaster) string {
	if bddOrdersMemoryExhausted(blasters) {
		return "memory admission allowance"
	}
	return "node budget"
}

// A deliberately narrow resource trace avoids printing entire symbolic terms.
func traceBDDResources(event string, bl *blaster, reservation uint64) {
	if os.Getenv("OAK_VERIFY_RESOURCE_TRACE") == "" {
		return
	}
	var memory runtime.MemStats
	runtime.ReadMemStats(&memory)
	fmt.Fprintf(os.Stderr, "bdd resources: %s order=%q budget=%d reservation=%d nodes=%d node_capacity=%d unique_slots=%d memo_slots=%d memo_resets=%d exhausted=%v memory_exhausted=%v heap_alloc=%d heap_inuse=%d heap_released=%d\n",
		event, bl.label, bl.bdd.budget, reservation, len(bl.bdd.nodes), cap(bl.bdd.nodes), len(bl.bdd.unique.entries), len(bl.bdd.memo.entries), bl.bdd.memo.resets, bl.bdd.exceeded, bl.bdd.memoryExhausted, memory.HeapAlloc, memory.HeapInuse, memory.HeapReleased)
}

// Resolve the process's subgroup and each visible ancestor, not just the
// mount root. A parent cgroup can be stricter than its leaf. Procfs escapes
// mount paths with octal sequences; decode only its four documented escapes.
func bddCgroupMemoryPairs(membership, mounts string) [][2]string {
	var out [][2]string
	unescape := strings.NewReplacer("\\040", " ", "\\011", "\t", "\\012", "\n", "\\134", "\\")
	for _, member := range strings.Split(membership, "\n") {
		parts := strings.SplitN(member, ":", 3)
		if len(parts) != 3 || !strings.HasPrefix(parts[2], "/") {
			continue
		}
		v2 := parts[1] == ""
		if !v2 && !strings.Contains(","+parts[1]+",", ",memory,") {
			continue
		}
		for _, mount := range strings.Split(mounts, "\n") {
			fields := strings.Fields(mount)
			separator := -1
			for i, field := range fields {
				if field == "-" {
					separator = i
					break
				}
			}
			if separator < 6 || separator+3 >= len(fields) {
				continue
			}
			if v2 && fields[separator+1] != "cgroup2" {
				continue
			}
			if !v2 && (fields[separator+1] != "cgroup" || !strings.Contains(","+fields[separator+3]+",", ",memory,")) {
				continue
			}
			root, mountpoint, group := path.Clean(unescape.Replace(fields[3])), path.Clean(unescape.Replace(fields[4])), path.Clean(parts[2])
			if !strings.HasPrefix(mountpoint, "/") {
				continue
			}
			relative := ""
			switch {
			case root == "/":
				relative = strings.TrimPrefix(group, "/")
			case group == root || group == "/": // namespace-relative mount root
			case strings.HasPrefix(group, root+"/"):
				relative = strings.TrimPrefix(group, root+"/")
			default:
				continue
			}
			for directory := path.Join(mountpoint, relative); ; directory = path.Dir(directory) {
				if v2 {
					out = append(out, [2]string{path.Join(directory, "memory.max"), path.Join(directory, "memory.current")})
				} else {
					out = append(out, [2]string{path.Join(directory, "memory.limit_in_bytes"), path.Join(directory, "memory.usage_in_bytes")})
				}
				if directory == mountpoint {
					break
				}
			}
		}
	}
	return out
}

var bddAdmissionDenials atomic.Uint64

// A denial can arise deep in bool-returning loop/split/pruning helpers. Track
// a conservative process-wide generation over Verify rather than losing its
// transient nature while those helpers unwind. A concurrent unrelated denial
// may prevent caching another negative result, which merely causes a retry.
// Proven results/refutations are independent of resources and remain durable.
func trackBDDResourceExhaustion(verdict *Verdict) func() {
	before := bddAdmissionDenials.Load()
	return func() {
		if verdict.Kind != VerdictProven && verdict.Kind != VerdictMismatch && bddAdmissionDenials.Load() != before {
			verdict.TransientResourceExhausted = true
		}
	}
}
