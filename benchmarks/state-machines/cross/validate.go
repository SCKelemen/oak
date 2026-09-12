// Go standard library: unicode/utf8.Valid over the shared input.
package main

import (
	"fmt"
	"os"
	"time"
	"unicode/utf8"
)

func main() {
	buf, err := os.ReadFile("input.bin")
	if err != nil {
		panic(err)
	}
	best := time.Duration(1 << 62)
	ok := false
	for r := 0; r < 5; r++ {
		t0 := time.Now()
		ok = utf8.Valid(buf)
		if d := time.Since(t0); d < best {
			best = d
		}
	}
	n := float64(len(buf))
	fmt.Printf("%-34s %6.2f ns/byte  %6.2f GB/s\n", "Go unicode/utf8.Valid", float64(best.Nanoseconds())/n, n/float64(best.Nanoseconds()))
	if !ok {
		os.Exit(1)
	}
}
