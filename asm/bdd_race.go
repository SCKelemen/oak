package asm

import (
	"sync"
	"sync/atomic"
)

// raceBDDOrders returns the first non-exhausted result, after cancelling and
// joining every other order and consuming their diagram stores. Only budget,
// completedNodes and exhaustion metadata survive. No previous worker can keep
// growing a store when the next proof begins.
// run owns its blaster until it returns, returns no diagram-backed storage,
// and reports true for exhaustion or an
// interrupted result. The final interrupted check also rejects partial results
// if cancellation arrived during a cache hit or counterexample extraction.
func raceBDDOrders[T any](blasters []*blaster, run func(*blaster) (T, bool)) (winner T, decided bool) {
	return raceBDDOrdersAdmitted(blasters, run, processBDDOrders)
}

// raceBDDOrdersAdmitted preserves every candidate order and its node allowance.
// Orders which cannot fit the finite admission estimate explicitly exhaust;
// queued orders stop only after a valid winner, and all owners are joined.
func raceBDDOrdersAdmitted[T any](blasters []*blaster, run func(*blaster) (T, bool), admission *bddOrderAdmission) (winner T, decided bool) {
	var stop atomic.Bool
	type attempt struct {
		result   T
		exceeded bool
	}
	results := make(chan attempt, len(blasters))
	var workers sync.WaitGroup
	requests := admission.enqueue(len(blasters))
	for i, bl := range blasters {
		bl.bdd.stop = &stop
		workers.Add(1)
		go func(bl *blaster) {
			defer workers.Done()
			reservation := bddOrderEstimate(bl.bdd.budget)
			if !admission.acquireQueued(requests[i], reservation, &stop) {
				bl.bdd.memoryExhausted = !stop.Load()
				if bl.bdd.memoryExhausted {
					bddAdmissionDenials.Add(1)
				}
				bl.bdd.exceeded = true
				traceBDDResources("denied", bl, reservation)
				releaseBDDStores(bl)
				results <- attempt{exceeded: true}
				return
			}
			traceBDDResources("start", bl, reservation)
			result, exceeded := run(bl)
			exceeded = exceeded || bl.bdd.interrupted()
			traceBDDResources("finish", bl, reservation)
			released := releaseBDDStores(bl)
			results <- attempt{result, exceeded}
			admission.cleanup(released)
			admission.release(reservation)
		}(bl)
	}
	for range blasters {
		if a := <-results; !a.exceeded && !decided {
			winner, decided = a.result, true
			stop.Store(true)
			admission.wake()
		}
	}
	workers.Wait()
	return winner, decided
}
