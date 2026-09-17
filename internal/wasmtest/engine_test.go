package wasmtest

import (
	"context"
	"errors"
	"fmt"
	"reflect"
	"strings"
	"sync"
	"testing"
	"time"
)

func TestWasmEngineExplicitSelection(t *testing.T) {
	for _, name := range []string{"node", "deno"} {
		t.Run(name, func(t *testing.T) {
			var looked []string
			e, err := selectEngine(t.Context(), name, func(got string) (string, error) {
				looked = append(looked, got)
				return "/local tools/" + got, nil
			}, func(context.Context, string) error {
				t.Fatal("explicit engine must not run redundant discovery probe")
				return nil
			})
			if err != nil || !reflect.DeepEqual(looked, []string{name}) {
				t.Fatalf("selection: %+v, %v, lookups %v", e, err, looked)
			}
			// Metacharacters and spaces stay ordinary argv elements, not shell text.
			script, argument := "console.log('$(not-a-command)')", "a; b $value"
			cmd := e.Command(t.Context(), script, argument)
			flag := "-e"
			if name == "deno" {
				flag = "eval"
			}
			want := []string{"/local tools/" + name, flag, script, argument}
			if cmd.Path != want[0] || !reflect.DeepEqual(cmd.Args, want) || cmd.WaitDelay != time.Second {
				t.Fatalf("unexpected process invocation: %q %q", cmd.Path, cmd.Args)
			}
			// Subsequent commands must not share a mutable argument slice.
			cmd.Args[2] = "changed"
			if next := e.Command(t.Context(), script); next.Args[2] != script {
				t.Fatal("arguments leaked across requests")
			}
		})
	}
}

func TestWasmEngineAutomaticFallback(t *testing.T) {
	var probes []string
	e, err := selectEngine(t.Context(), "", func(name string) (string, error) {
		return "/tools/" + name, nil
	}, func(ctx context.Context, path string) error {
		deadline, ok := ctx.Deadline()
		if remaining := time.Until(deadline); !ok || remaining <= 0 || remaining > probeTimeout {
			t.Fatal("automatic probe lost its three-second budget")
		}
		probes = append(probes, path)
		if strings.HasSuffix(path, "node") {
			return errors.New("missing dynamic library")
		}
		return nil
	})
	if err != nil || e.name != "deno" || !reflect.DeepEqual(probes, []string{"/tools/node", "/tools/deno"}) {
		t.Fatalf("fallback: %+v, %v, probes %v", e, err, probes)
	}
	probes = nil
	e, err = selectEngine(t.Context(), "", func(name string) (string, error) {
		return name, nil
	}, func(_ context.Context, path string) error { probes = append(probes, path); return nil })
	if err != nil || e.name != "node" || !reflect.DeepEqual(probes, []string{"node"}) {
		t.Fatal("working first engine was not retained")
	}
}

func TestWasmEngineWhitelistAndCancellation(t *testing.T) {
	lookup := func(string) (string, error) { t.Fatal("unexpected process lookup"); return "", nil }
	probe := func(context.Context, string) error { t.Fatal("unexpected process probe"); return nil }
	for _, name := range []string{"auto", "Node", "node --eval", "/bin/node", "deno; echo bad", " "} {
		if _, err := selectEngine(t.Context(), name, lookup, probe); err == nil {
			t.Fatalf("unrecognized engine %q accepted", name)
		}
	}
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	if _, err := selectEngine(ctx, "", lookup, probe); !errors.Is(err, context.Canceled) {
		t.Fatalf("cancellation lost: %v", err)
	}
}

func TestWasmEngineReportsDiscoveryFailures(t *testing.T) {
	_, err := selectEngine(t.Context(), "", func(name string) (string, error) {
		return name, nil
	}, func(_ context.Context, name string) error {
		if name == "node" {
			return errors.New("dyld: missing library")
		}
		return context.DeadlineExceeded
	})
	for _, want := range []string{"node: dyld: missing library", "deno: context deadline exceeded"} {
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Fatalf("missing %q: %v", want, err)
		}
	}
}

type recordingReporter struct{ fatal, skipped, logged string }

func (*recordingReporter) Helper()                        {}
func (r *recordingReporter) Fatalf(f string, args ...any) { r.fatal = fmt.Sprintf(f, args...) }
func (r *recordingReporter) Skipf(f string, args ...any)  { r.skipped = fmt.Sprintf(f, args...) }
func (r *recordingReporter) Logf(f string, args ...any)   { r.logged = fmt.Sprintf(f, args...) }

func TestWasmEngineRequiredAndExplicitNeverSkip(t *testing.T) {
	for _, selected := range []string{"", "node", "deno", "invalid"} {
		for _, required := range []bool{false, true} {
			r := &recordingReporter{}
			require(r, t.Context(), selected, required, func(string) (string, error) {
				return "", errors.New("executable not found")
			}, func(context.Context, string) error { t.Fatal("probed missing executable"); return nil })
			mustFail := required || selected != ""
			if (r.fatal != "") != mustFail || (r.skipped != "") == mustFail || r.logged != "" {
				t.Fatalf("selected=%q required=%t: %+v", selected, required, r)
			}
		}
	}
	r := &recordingReporter{}
	require(r, t.Context(), "node", true, func(string) (string, error) { return "/tools/node", nil }, nil)
	if r.fatal != "" || r.skipped != "" || !strings.Contains(r.logged, "/tools/node") {
		t.Fatalf("successful explicit selection: %+v", r)
	}
}

func TestWasmEngineOutputIsBounded(t *testing.T) {
	var output boundedOutput
	if n, err := output.Write([]byte("short")); n != 5 || err != nil || output.String() != "short" {
		t.Fatal("short diagnostic lost")
	}
	var wg sync.WaitGroup
	for i := 0; i < 8; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			input := []byte(strings.Repeat("x", maxProbeOutput*4))
			if n, err := output.Write(input); n != len(input) || err != nil {
				t.Error("truncating capture did not drain the process output")
			}
			_ = output.String()
		}()
	}
	wg.Wait()
	if got := output.String(); !strings.HasPrefix(got, "short") || !strings.HasSuffix(got, " [output truncated]") || len(output.data) != maxProbeOutput {
		t.Fatalf("unbounded or corrupt capture: %d bytes", len(got))
	}
}

func TestWasmEngineCommandRejectsInvalidEngine(t *testing.T) {
	for _, engine := range []Engine{{}, {name: "node"}, {name: "sh", path: "/bin/sh"}} {
		func() {
			defer func() {
				if recover() == nil {
					t.Error("invalid engine formed a command")
				}
			}()
			engine.Command(t.Context(), "ignored")
		}()
	}
}
