package asm

import (
	"sync"
	"sync/atomic"
)

// raceBDDOrders returns the first non-exhausted result, after cancelling and
// joining every other order. A caller may start the next proof or inspect the
// diagrams immediately on return; no previous worker can keep growing a store.
// run owns its blaster until it returns and reports true for exhaustion or an
// interrupted result. The final interrupted check also rejects partial results
// if cancellation arrived during a cache hit or counterexample extraction.
func raceBDDOrders[T any](blasters []*blaster, run func(*blaster) (T, bool)) (winner T, decided bool) {
	var stop atomic.Bool
	type attempt struct {
		result   T
		exceeded bool
	}
	results := make(chan attempt, len(blasters))
	var workers sync.WaitGroup
	for _, bl := range blasters {
		bl.bdd.stop = &stop
		workers.Add(1)
		go func(bl *blaster) {
			defer workers.Done()
			result, exceeded := run(bl)
			results <- attempt{result, exceeded || bl.bdd.interrupted()}
		}(bl)
	}
	for range blasters {
		if a := <-results; !a.exceeded && !decided {
			winner, decided = a.result, true
			stop.Store(true)
		}
	}
	workers.Wait()
	return winner, decided
}
