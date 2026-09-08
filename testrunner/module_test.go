package testrunner

import (
	"path/filepath"
	"strings"
	"testing"
)

// A directory whose files open with package clauses is compiled through the
// module loader with its *_test.oak files, so tests can exercise pub members,
// imported packages, and the simulation profile with mangled root symbols.
func TestModulePackages(t *testing.T) {
	dir := fixture(t, map[string]string{
		"oak.mod": "module example.com/os\noak 0.1.0\n",
		"sched/queue.oak": `package sched

pub Queue: type = struct { count: u32 }

pub queue_push: (q: [*]Queue): Bool {
  q[0].count < u32(2) ? { q[0].count = q[0].count + u32(1); true } | { false }
}
`,
		"sched/queue_test.oak": `package sched

import(testing)

TestPush: (): () {
  storage: [1]Queue
  q: [*]Queue = span(&storage)
  q[0] = Queue { count: u32(0) }
  test_check(queue_push(q), u32(1))
  test_check(queue_push(q), u32(2))
  test_check(!queue_push(q), u32(3))
}

PropertyPushBound: (data: []u8): () {
  storage: [1]Queue
  q: [*]Queue = span(&storage)
  q[0] = Queue { count: u32(0) }
  i: u32 = u32(0)
  while i < len(data) { pushed: Bool = queue_push(q); i = i + u32(1) }
  test_check(q[0].count <= u32(2), u32(4))
  test_check(len(data) < u32(3), u32(5))
}

SimQueueClock: (data: []u8): () {
  clock_storage: [1]SimClock
  clock: [*]SimClock = span(&clock_storage)
  clock[0] = SimClock { now: u64(len(data)) }
  test_check(clock[0].now < u64(300), u32(6))
}
`,
		"app/app.oak": `package main

import("example.com/os/sched")

pub fill: (): u32 {
  storage: [1]sched.Queue
  q: [*]sched.Queue = span(&storage)
  q[0] = sched.Queue { count: u32(0) }
  first: Bool = sched.queue_push(q)
  second: Bool = sched.queue_push(q)
  q[0].count
}
`,
		"app/app_test.oak": `package main

import(testing)

TestFillUsesImportedPackage: (): () { test_check(fill() == u32(2), u32(7)) }
`,
	})
	code, results, stderr := runCLI(t, "-runs", "8", filepath.Join(dir, "app"), filepath.Join(dir, "sched"))
	if code != 1 || len(results) != 4 {
		t.Fatalf("%d %+v %s", code, results, stderr)
	}
	byName := map[string]Result{}
	for _, r := range results {
		byName[r.Name] = r
	}
	for _, name := range []string{"TestPush", "SimQueueClock", "TestFillUsesImportedPackage"} {
		if byName[name].Status != "pass" {
			t.Fatalf("%s: %+v", name, byName[name])
		}
	}
	bound := byName["PropertyPushBound"]
	if bound.Status != "fail" || bound.Failure != "invariant:5" {
		t.Fatalf("property: %+v", bound)
	}
	a, err := readArtifact(bound.Artifact, 256)
	if err != nil || len(a.Input) != 3 {
		t.Fatalf("minimized module failure: %+v %v", a, err)
	}
	code, replay, _ := runCLI(t, "-replay", bound.Artifact, filepath.Join(dir, "sched"))
	if code != 1 || replay[0].Failure != "reproduced invariant:5" {
		t.Fatalf("module replay: %d %+v", code, replay)
	}
	if _, err := Discover([]string{fixture(t, map[string]string{"a.oak": "package a\n", "a_test.oak": "TestA: (): () {}"})}); err == nil || !strings.Contains(err.Error(), "package clause") {
		t.Fatalf("mixed package clauses accepted: %v", err)
	}
}
