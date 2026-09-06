package main

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/serialize"
)

func main() {
	allPassed := true
	scratchRoot := filepath.Join(os.TempDir(), "oak_golden_verify")
	defer os.RemoveAll(scratchRoot)

	for _, tc := range serialize.GoldenCases() {
		if tc.Skip {
			fmt.Printf("Skipping '%s' (known issues)\n", tc.Name)
			continue
		}

		fmt.Printf("Verifying golden files for '%s'...\n", tc.Name)
		mismatches, err := serialize.VerifyGoldenCase(tc, "golden", filepath.Join(scratchRoot, tc.Name))
		if err != nil {
			fmt.Fprintf(os.Stderr, "❌ %s: %v\n", tc.Name, err)
			fmt.Fprintf(os.Stderr, "   (Run 'go run ./cmd/generate_golden' to regenerate)\n")
			allPassed = false
			continue
		}
		if len(mismatches) > 0 {
			for _, mismatch := range mismatches {
				fmt.Fprintf(os.Stderr, "❌ %s\n", mismatch)
			}
			allPassed = false
			continue
		}
		fmt.Printf("✅ %s: All golden files match\n", tc.Name)
	}

	if !allPassed {
		fmt.Fprintln(os.Stderr, "\n❌ Some golden files do not match expected outputs")
		os.Exit(1)
	}
	fmt.Println("\n✅ All golden files match expected outputs")
}
