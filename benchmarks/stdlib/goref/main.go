// goref runs the Go standard-library twins of the Oak stdlib benchmarks and
// prints the same JSON lines as the C runner: one preflight line per
// workload with its checksum, then one line per timed sample.
//
//	go run ./benchmarks/stdlib/goref <scale> <samples> [workload-prefix]
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strconv"
	"strings"
	"time"
)

type line struct {
	Event    string `json:"event"`
	Workload string `json:"workload"`
	Backend  string `json:"backend,omitempty"`
	Sample   int    `json:"sample,omitempty"`
	NS       uint64 `json:"ns,omitempty"`
	Items    uint64 `json:"items"`
	Bytes    uint64 `json:"bytes"`
	Checksum uint64 `json:"checksum"`
}

func emit(l line) {
	encoded, err := json.Marshal(l)
	if err != nil {
		panic(err)
	}
	fmt.Println(string(encoded))
}

func main() {
	if len(os.Args) < 3 || len(os.Args) > 4 {
		fmt.Fprintln(os.Stderr, "usage: goref <scale> <samples> [workload-prefix]")
		os.Exit(2)
	}
	scale, err := strconv.ParseFloat(os.Args[1], 64)
	if err != nil || !(scale > 0 && scale <= 16) {
		fmt.Fprintln(os.Stderr, "scale must be in (0, 16]")
		os.Exit(2)
	}
	samples, err := strconv.Atoi(os.Args[2])
	if err != nil || samples < 1 || samples > 100 {
		fmt.Fprintln(os.Stderr, "samples must be in 1..100")
		os.Exit(2)
	}
	prefix := ""
	if len(os.Args) == 4 {
		prefix = os.Args[3]
	}
	// Each setup builds every corpus of its package; run it once per package.
	prepared := map[string]bool{}
	for _, w := range workloads {
		if !strings.HasPrefix(w.name, prefix) {
			continue
		}
		pkg := strings.SplitN(w.name, "/", 2)[0]
		if !prepared[pkg] {
			w.setup(scale)
			prepared[pkg] = true
		}
		expected := w.run()
		emit(line{Event: "preflight", Workload: w.name, Items: w.items, Bytes: w.bytes, Checksum: expected})
		for sample := 0; sample < samples; sample++ {
			start := time.Now()
			checksum := w.run()
			ns := uint64(time.Since(start).Nanoseconds())
			if checksum != expected {
				fmt.Fprintln(os.Stderr, "timed checksum mismatch in", w.name)
				os.Exit(1)
			}
			emit(line{Event: "sample", Workload: w.name, Backend: w.backend, Sample: sample, NS: ns, Items: w.items, Bytes: w.bytes, Checksum: checksum})
		}
	}
}
