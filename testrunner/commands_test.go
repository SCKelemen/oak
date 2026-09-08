package testrunner

import (
	"context"
	"reflect"
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
