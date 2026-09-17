// Package wasmtest selects independent JavaScript engines for compiler tests.
// It is test infrastructure, not part of compilation or semantic admission.
package wasmtest

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"strings"
	"sync"
	"testing"
	"time"
)

const probeTimeout = 3 * time.Second
const maxProbeOutput = 4096

type Engine struct{ name, path string }

// Command constructs an invocation without a shell. Selection is not evidence
// of correctness: callers must execute this command and check its result.
func (e Engine) Command(ctx context.Context, script string, args ...string) *exec.Cmd {
	var flag string
	switch e.name {
	case "node":
		flag = "-e"
	case "deno":
		flag = "eval"
	default:
		panic("wasmtest: invalid engine")
	}
	if e.path == "" {
		panic("wasmtest: missing executable")
	}
	cmd := exec.CommandContext(ctx, e.path, append([]string{flag, script}, args...)...)
	cmd.WaitDelay = time.Second // a descendant must not keep inherited output pipes open forever
	return cmd
}

type reporter interface {
	Helper()
	Logf(string, ...any)
	Fatalf(string, ...any)
	Skipf(string, ...any)
}

type lookupFunc func(string) (string, error)
type probeFunc func(context.Context, string) error

// Require honors OAK_WASM_TEST_ENGINE=node|deno. Explicit selection skips only
// the version probe; the actual validation/execution test still must pass.
// Automatic discovery keeps its bounded node-then-deno fallback. Missing engines
// are fatal in required mode; a broken explicit configuration is always fatal.
func Require(t *testing.T) Engine {
	t.Helper()
	return require(t, t.Context(), os.Getenv("OAK_WASM_TEST_ENGINE"),
		os.Getenv("OAK_REQUIRE_WASM_TESTS") == "1", exec.LookPath, probeVersion)
}

func require(t reporter, ctx context.Context, selected string, required bool, lookup lookupFunc, probe probeFunc) Engine {
	t.Helper()
	e, err := selectEngine(ctx, selected, lookup, probe)
	if err != nil {
		if required || selected != "" {
			t.Fatalf("independent Wasm engine required: %v", err)
		} else {
			t.Skipf("independent Wasm engine unavailable: %v", err)
		}
		return Engine{}
	}
	t.Logf("independent Wasm engine: %s (%s)", e.name, e.path)
	return e
}

func selectEngine(ctx context.Context, selected string, lookup lookupFunc, probe probeFunc) (Engine, error) {
	names := []string{"node", "deno"}
	if selected != "" {
		if selected != "node" && selected != "deno" {
			return Engine{}, fmt.Errorf("OAK_WASM_TEST_ENGINE must be node or deno, not %q", selected)
		}
		names = []string{selected}
	}
	var failures []string
	for _, name := range names {
		if err := ctx.Err(); err != nil {
			return Engine{}, err
		}
		path, err := lookup(name)
		if err == nil && selected == "" {
			probeCtx, cancel := context.WithTimeout(ctx, probeTimeout)
			err = probe(probeCtx, path)
			cancel()
		}
		if err == nil {
			return Engine{name: name, path: path}, nil
		}
		failures = append(failures, fmt.Sprintf("%s: %v", name, err))
	}
	return Engine{}, fmt.Errorf("%s", strings.Join(failures, "; "))
}

func probeVersion(ctx context.Context, path string) error {
	cmd := exec.CommandContext(ctx, path, "--version")
	cmd.WaitDelay = time.Second
	var output boundedOutput
	cmd.Stdout, cmd.Stderr = &output, &output
	err := cmd.Run()
	if ctx.Err() != nil {
		err = fmt.Errorf("%w (process: %v)", ctx.Err(), err)
	}
	if err != nil && output.String() != "" {
		return fmt.Errorf("%w; output: %s", err, output.String())
	}
	return err
}

// Drain all writes without retaining unbounded output from a broken executable.
type boundedOutput struct {
	mu        sync.Mutex
	data      []byte
	truncated bool
}

func (b *boundedOutput) Write(p []byte) (int, error) {
	b.mu.Lock()
	defer b.mu.Unlock()
	keep := min(len(p), maxProbeOutput-len(b.data))
	b.data = append(b.data, p[:keep]...)
	b.truncated = b.truncated || keep < len(p)
	return len(p), nil
}

func (b *boundedOutput) String() string {
	b.mu.Lock()
	defer b.mu.Unlock()
	if b.truncated {
		return string(b.data) + " [output truncated]"
	}
	return string(b.data)
}
