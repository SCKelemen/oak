package main

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

// synthesizeCommand fixes the source bytes before invoking candidate search.
// Candidate input is data, not a source overlay or an executable agent command.
func synthesizeCommand(path, property, candidatePath string, cases, rounds int, asJSON bool, stdout, stderr io.Writer) int {
	source, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: synthesis: %v\n", err)
		return 2
	}
	options := prove.SynthesisOptions{Cases: cases, MaxRounds: rounds}
	if candidatePath != "" {
		file, err := os.Open(candidatePath)
		if err != nil {
			fmt.Fprintf(stderr, "oak prove: synthesis: %v\n", err)
			return 2
		}
		defer file.Close()
		// Bound the transport before decoding, as well as each parsed predicate.
		bytes, err := io.ReadAll(io.LimitReader(file, (1<<20)+1))
		if err != nil || len(bytes) > 1<<20 {
			fmt.Fprintln(stderr, "oak prove: synthesis: cannot read candidates within the 1 MiB input limit")
			return 2
		}
		decoder := json.NewDecoder(strings.NewReader(string(bytes)))
		if err := decoder.Decode(&options.Candidates); err != nil || options.Candidates == nil {
			fmt.Fprintln(stderr, "oak prove: synthesis: candidates must be a JSON array of predicate strings (not null)")
			return 2
		}
		var trailing interface{}
		if err := decoder.Decode(&trailing); err != io.EOF {
			fmt.Fprintln(stderr, "oak prove: synthesis: trailing candidate data")
			return 2
		}
	}
	report, err := prove.SynthesizeInvariant(compiler.SourceText{Path: path, Text: string(source)}, property, options)
	if err != nil {
		fmt.Fprintf(stderr, "oak prove: %v\n", err)
		return 2
	}
	if asJSON {
		encoder := json.NewEncoder(stdout)
		encoder.SetIndent("", "  ")
		if err := encoder.Encode(report); err != nil {
			fmt.Fprintf(stderr, "oak prove: synthesis: %v\n", err)
			return 2
		}
	} else {
		fmt.Fprintf(stdout, "%-9s %s: %s\n", report.Status, report.Property, report.Detail)
		fmt.Fprintf(stdout, "source SHA-256: %s\n", report.SourceSHA256)
		if report.Invariant != "" {
			fmt.Fprintf(stdout, "invariant: %s\n", report.Invariant)
		}
		for _, rejected := range report.Rejected {
			fmt.Fprintf(stdout, "dropped (round %d) %s: %s (%s)\n", rejected.Round, rejected.Predicate, rejected.Check.Status, rejected.Check.Detail)
		}
		for _, check := range report.Checks {
			fmt.Fprintf(stdout, "%-9s %s: %s\n", check.Status, check.Name, check.Detail)
		}
	}
	if report.Status == prove.Decided {
		return 0
	}
	return 1
}
