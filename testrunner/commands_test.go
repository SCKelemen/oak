package testrunner

import (
	"bytes"
	"context"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func TestCommandShrinkPreservesDependencies(t *testing.T) {
	input := encodeCommands([]Command{{9, 0, 0}, {1, 7, 0}, {2, 7, 100}, {9, 0, 0}})
	calls := 0
	fails := func(data []byte) bool {
		calls++
		if len(data)%12 != 0 {
			t.Fatal("split command")
		}
		created := map[uint32]bool{}
		failed := false
		for _, c := range decodeCommands(data) {
			switch c.Kind {
			case 1:
				created[c.Target] = true
			case 2:
				if !created[c.Target] {
					return false
				}
				failed = c.Value >= 3
			case 9:
			default:
				t.Fatal("changed command kind")
			}
		}
		return failed
	}
	got := decodeCommands(MinimizeCommands(context.Background(), input, 200, fails))
	want := []Command{{1, 7, 0}, {2, 7, 3}}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("got %+v, want %+v", got, want)
	}
	if calls > 200 {
		t.Fatal("exceeded budget")
	}
}

func TestCommandGeneratorDiscovery(t *testing.T) {
	for _, source := range []string{
		"GeneratePropertyMissing: (data: []u8): () {}",
		"GenerateFuzzBytes: (data: []u8): () {}\nFuzzBytes: (data: []u8): () {}",
		"GeneratePropertyBad: (): () {}\nPropertyBad: (data: []u8): () {}",
	} {
		dir := fixture(t, map[string]string{"a_test.oak": source})
		if _, err := Discover([]string{dir}); err == nil {
			t.Fatalf("accepted %s", source)
		}
	}
}

func TestNativeCommandsShrinkReplay(t *testing.T) {
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
GeneratePropertyCommands: (data: []u8): () {
 testing_command(TestCommand { kind: u32(1), target: u32(7), value: u32(0) })
 testing_command(TestCommand { kind: u32(2), target: u32(7), value: u32(100) })
}
PropertyCommands: (data: []u8): () {
 count: u32 = test_command_count(data)
 test_assume(count == u32(2))
 first: TestCommand = test_command_at(data, u32(0))
 second: TestCommand = test_command_at(data, u32(1))
 test_assume(first.kind == u32(1) && second.kind == u32(2) && first.target == second.target)
 testing_trace(u32(400), u64(first.target), u64(second.value))
 test_check(second.value < u32(3), u32(8001))
}`})
	code, results, stderr := runCLI(t, "-runs", "1", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:8001" {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	result := results[0]
	want := []Command{{1, 7, 0}, {2, 7, 3}}
	if !reflect.DeepEqual(result.Commands, want) {
		t.Fatalf("commands: %+v", result)
	}
	a, err := readArtifact(result.Artifact, 256)
	if err != nil || a.InputFormat != commandFormat {
		t.Fatalf("artifact %+v %v", a, err)
	}
	code, results, stderr = runCLI(t, "-replay", result.Artifact, dir)
	if code != 1 || results[0].Failure != "reproduced invariant:8001" || !reflect.DeepEqual(results[0].Commands, want) {
		t.Fatalf("replay %d %+v %s", code, results, stderr)
	}
	code, results, stderr = runCLI(t, "-runs", "1", "-seed", "99", dir)
	if code != 1 || results[0].Cases != 1 {
		t.Fatalf("corpus %d %+v %s", code, results, stderr)
	}
}

// The command-generated IRQ example must reduce the injected lost-edge bug to
// the four-command counterexample while every intermediate candidate stays a
// legal history: deleting the enabling command invalidates the acknowledgement.
func TestIRQCommandMutationDetected(t *testing.T) {
	files := map[string]string{}
	for _, name := range []string{"irq.oak", "irq_test.oak"} {
		data, err := os.ReadFile(filepath.Join("..", "examples", "testing", name))
		if err != nil {
			t.Fatal(err)
		}
		files[name] = string(data)
	}
	original := "action == u32(2) ? { state[0].latched = true }"
	mutant := "action == u32(2) && !state[0].active ? { state[0].latched = true }"
	if !strings.Contains(files["irq.oak"], original) {
		t.Fatal("mutation site changed")
	}
	files["irq.oak"] = strings.Replace(files["irq.oak"], original, mutant, 1)
	// enable, level up, inject, level down, ack, eoi, inject, ack, inject.
	var history []Command
	for _, kind := range []uint32{0, 3, 2, 4, 5, 6, 2, 5, 2} {
		history = append(history, Command{Kind: kind})
	}
	files["testdata/oak/PropertyIrqCommands/lost-edge.bin"] = string(encodeCommands(history))
	dir := fixture(t, files)
	code, results, stderr := runCLI(t, "-run", "^PropertyIrqCommands$", "-runs", "1", dir)
	if code != 1 || len(results) != 1 || results[0].Failure != "invariant:2011" {
		t.Fatalf("mutation escaped: %d %+v %s", code, results, stderr)
	}
	want := []Command{{Kind: 0}, {Kind: 2}, {Kind: 5}, {Kind: 2}}
	if !reflect.DeepEqual(results[0].Commands, want) {
		t.Fatalf("unexpected minimized history: %+v", results[0].Commands)
	}
	if len(results[0].Trace) != 4 || results[0].Trace[3].ID != 202 || results[0].Trace[3].A != 2 {
		t.Fatalf("trace does not describe the minimized history: %+v", results[0].Trace)
	}
	code, replay, _ := runCLI(t, "-replay", results[0].Artifact, dir)
	if code != 1 || replay[0].Failure != "reproduced invariant:2011" || !reflect.DeepEqual(replay[0].Commands, want) {
		t.Fatalf("replay: %d %+v", code, replay)
	}
}

// Command minimization must keep every candidate aligned, never change a kind,
// never grow, and never lose a failure the predicate still reports.
func FuzzMinimizeCommands(t *testing.F) {
	t.Add(encodeCommands([]Command{{1, 7, 0}, {2, 7, 100}, {9, 0, 0}}))
	t.Fuzz(func(t *testing.T, input []byte) {
		if len(input) > 24*commandWidth || len(input)%commandWidth != 0 {
			t.Skip()
		}
		original := append([]byte(nil), input...)
		kinds := map[uint32]int{}
		for _, c := range decodeCommands(input) {
			kinds[c.Kind]++
		}
		predicate := func(data []byte) bool {
			if len(data)%commandWidth != 0 {
				t.Fatal("unaligned candidate")
			}
			seen := map[uint32]int{}
			failed := false
			for _, c := range decodeCommands(data) {
				seen[c.Kind]++
				if kinds[c.Kind] < seen[c.Kind] {
					t.Fatal("invented command kind")
				}
				if c.Kind == 2 && c.Value >= 3 {
					failed = true
				}
			}
			return failed
		}
		best := MinimizeCommands(context.Background(), input, 100, predicate)
		if predicate(input) && !predicate(best) {
			t.Fatal("lost failure")
		}
		if len(best) > len(input) || !bytes.Equal(input, original) {
			t.Fatal("invalid shrink")
		}
	})
}
