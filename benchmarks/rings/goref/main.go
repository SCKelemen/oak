// The Go reference for the rings benchmark: buffered channels carrying the
// same item counts between the same thread shapes, timed the same way.
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"sync"
	"time"
)

const items = 2000000
const producers = 4

type result struct {
	Ring      string  `json:"ring"`
	Threads   string  `json:"threads"`
	Items     int     `json:"items"`
	NsPerItem float64 `json:"ns_per_item"`
}

func emit(ring, threads string, elapsed time.Duration) {
	line, _ := json.Marshal(result{ring, threads, items, float64(elapsed.Nanoseconds()) / items})
	fmt.Println(string(line))
}

func main() {
	// SPSC: one channel, one producer, one consumer.
	ch := make(chan uint32, 1024)
	var sum uint64
	start := time.Now()
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		for v := range ch {
			sum += uint64(v)
		}
	}()
	for i := uint32(1); i <= items; i++ {
		ch <- i
	}
	close(ch)
	wg.Wait()
	check(sum, uint64(items)*(items+1)/2, "spsc")
	emit("spsc", "1 producer, 1 consumer", time.Since(start))

	for _, shape := range []struct {
		name      string
		consumers int
	}{{"mpsc", 1}, {"mpmc", producers}} {
		ch := make(chan uint32, 1024)
		sums := make([]uint64, shape.consumers)
		start := time.Now()
		var cw, pw sync.WaitGroup
		for c := 0; c < shape.consumers; c++ {
			cw.Add(1)
			go func(c int) {
				defer cw.Done()
				for v := range ch {
					sums[c] += uint64(v)
				}
			}(c)
		}
		for p := 0; p < producers; p++ {
			pw.Add(1)
			go func() {
				defer pw.Done()
				for i := uint32(1); i <= items/producers; i++ {
					ch <- i
				}
			}()
		}
		pw.Wait()
		close(ch)
		cw.Wait()
		var total uint64
		for _, s := range sums {
			total += s
		}
		n := uint64(items / producers)
		check(total, producers*(n*(n+1)/2), shape.name)
		emit(shape.name, fmt.Sprintf("%d producers, %d consumers", producers, shape.consumers), time.Since(start))
	}
}

func check(got, want uint64, ring string) {
	if got != want {
		fmt.Fprintf(os.Stderr, "%s: checksum %d, want %d\n", ring, got, want)
		os.Exit(1)
	}
}
