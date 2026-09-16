package asm

import (
	"sync"
	"testing"
)

func TestTermEvaluatorForkedConcurrentEvaluation(t *testing.T) {
	x := paramTerm("x", 32)
	y := paramTerm("y", 32)
	root := binaryTerm("add", binaryTerm("mul", x, constTerm(3, 32)), y)
	template := newTermEvaluator(root)
	rootID := root.id

	const attempts = 32
	results := make([]uint64, attempts)
	var wait sync.WaitGroup
	for index := range attempts {
		wait.Add(1)
		go func() {
			defer wait.Done()
			evaluator := template.fork()
			results[index] = evaluator.evaluate(root, map[string]uint64{
				"x": uint64(index), "y": uint64(index + 7),
			})
		}()
	}
	wait.Wait()

	if root.id != rootID {
		t.Fatalf("forked evaluation changed root id from %d to %d", rootID, root.id)
	}
	for index, got := range results {
		if want := uint64(index*4 + 7); got != want {
			t.Fatalf("fork %d = %d, want %d", index, got, want)
		}
	}
}
