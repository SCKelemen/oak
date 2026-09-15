package asm

import (
	"sync"
	"testing"
)

// The BDD variable orders evaluate the same term DAG concurrently. Numbering
// belongs to each evaluator; constructing one must never mutate the shared DAG.
func TestTermEvaluatorNumbersSharedTermsConcurrently(t *testing.T) {
	root := binaryTerm("add", paramTerm("x", 32), constTerm(1, 32))
	start := make(chan struct{})
	wrong := make(chan uint64, 16)
	var workers sync.WaitGroup
	for range 16 {
		workers.Add(1)
		go func() {
			defer workers.Done()
			<-start
			for range 64 {
				evaluator := newTermEvaluator(root)
				if got := evaluator.evaluate(root, map[string]uint64{"x": 41}); got != 42 {
					wrong <- got
					return
				}
			}
		}()
	}
	close(start)
	workers.Wait()
	close(wrong)
	for got := range wrong {
		t.Errorf("shared term evaluated to %d, want 42", got)
	}
}
