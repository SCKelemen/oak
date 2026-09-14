package compiler

import (
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/diagnostic"
)

// The verdict cache (compiler/verdict_cache.go): a second build of the same
// program takes every verdict from the cache; a change to a callee's body
// re-verifies the callee and its callers and no other body; WithVerifyFresh
// bypasses the cache. The program carries a unique constant so that every
// run of this test starts cold whatever the cache holds.
func TestVerdictCache(t *testing.T) {
	requireArm64Host(t)
	stamp := fmt.Sprintf("%d", time.Now().UnixNano()%1000000007)
	program := func(incBody string) string {
		return "STAMP: u32 = u32(" + stamp + ")\n" +
			"inc: (a: u32) -> u32 = " + incBody + "\n" +
			"twice: (a: u32) -> u32 = inc(a) + inc(a)\n" +
			"other: (a: u32) -> u32 = a * u32(3)\n" +
			"main: (): i32 { assert(twice(u32(1)) > u32(0))\n  assert(other(u32(1)) == u32(3))\n  0 }\n"
	}
	tally := func(source string, fresh bool) (fromCache, verified int, verdicts map[string]string) {
		t.Helper()
		verdicts = map[string]string{}
		comp := New().WithSource("cache.oak", source).WithNativeBodies()
		if fresh {
			comp = comp.WithVerifyFresh()
		}
		comp = comp.WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
			if d.Source != "native" {
				return
			}
			if n, _ := fmt.Sscanf(d.Message, "native backend: %d of %d verdicts from the verdict cache", &fromCache, &verified); n == 2 {
				return
			}
			if strings.HasPrefix(d.Message, "native backend: asm unit ") {
				rest := strings.TrimPrefix(d.Message, "native backend: asm unit ")
				if colon := strings.IndexByte(rest, ':'); colon > 0 {
					verdicts[rest[:colon]] = rest
				}
			}
		})
		if _, err := comp.EmitNative(HostObjectFormat()).Get(); err != nil {
			t.Fatalf("compile: %v", err)
		}
		return fromCache, verified, verdicts
	}
	cold, total, first := tally(program("a + u32(1)"), false)
	if cold != 0 || total < 3 {
		t.Fatalf("a cold build must verify every body itself, got %d of %d from the cache", cold, total)
	}
	warm, again, second := tally(program("a + u32(1)"), false)
	if warm != total || again != total {
		t.Fatalf("a second build of the same program must take every verdict from the cache, got %d of %d", warm, again)
	}
	for name, verdict := range first {
		if second[name] != verdict {
			t.Errorf("%s: the cached verdict differs:\n  %s\n  %s", name, verdict, second[name])
		}
	}
	// A change to inc's body invalidates inc, its caller twice, and main
	// (which reaches inc through twice); other keeps its key.
	changed, changedTotal, _ := tally(program("a + u32(2)"), false)
	if changedTotal != total || changed != 1 {
		t.Fatalf("after a callee change exactly the bodies reaching it must be re-verified, got %d of %d from the cache", changed, changedTotal)
	}
	fresh, freshTotal, _ := tally(program("a + u32(2)"), true)
	if fresh != 0 || freshTotal != total {
		t.Fatalf("WithVerifyFresh must bypass the cache, got %d of %d", fresh, freshTotal)
	}
}
