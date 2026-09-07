package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/SCKelemen/oak/packageapi"
)

func readSnapshot(path string) (packageapi.Snapshot, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return packageapi.Snapshot{}, err
	}
	var snapshot packageapi.Snapshot
	if err := json.Unmarshal(data, &snapshot); err != nil {
		return packageapi.Snapshot{}, err
	}
	return snapshot, nil
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: oak-semver PREVIOUS_API.json CURRENT_API.json")
		os.Exit(2)
	}
	previous, err := readSnapshot(os.Args[1])
	if err != nil {
		fmt.Fprintf(os.Stderr, "previous snapshot: %v\n", err)
		os.Exit(2)
	}
	current, err := readSnapshot(os.Args[2])
	if err != nil {
		fmt.Fprintf(os.Stderr, "current snapshot: %v\n", err)
		os.Exit(2)
	}
	report, err := packageapi.Enforce(previous, current)
	for _, change := range report.Changes {
		fmt.Printf("%s: %s (%s)\n", change.Name, change.Level, change.Reason)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Printf("version %s is valid for a %s API change\n", current.Version, report.Required)
}
