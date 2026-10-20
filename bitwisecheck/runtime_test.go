package bitwisecheck

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"
)

func fixture(t *testing.T) [4][]byte {
	t.Helper()
	var in [4][]byte
	for n, name := range []string{"source.fixture", "wasm.fixture", "arm.fixture", "rv.fixture"} {
		b, err := os.ReadFile(filepath.Join("testdata", name))
		if err != nil {
			t.Fatal(err)
		}
		in[n] = b
	}
	return in
}
func TestZeroAuthority(t *testing.T) {
	// No fake successful bundle: inspect representation on an invalid zero value.
	typ := reflect.TypeFor[CheckedBundle]()
	for _, name := range []string{"source", "wasm", "arm", "rv"} {
		field, ok := typ.FieldByName(name)
		if !ok || field.Type.Kind() != reflect.String {
			t.Fatalf("%s exposes mutable slice storage to safe reflection", name)
		}
	}

	for _, i := range []*Installation{nil, {}} {
		if i.Valid() {
			t.Fatal("zero installation valid")
		}
		if b, e := i.CheckBundle(context.Background(), []byte{1}, []byte{1}, []byte{1}, []byte{1}); b != nil || !errors.Is(e, ErrInvalidInstallation) {
			t.Fatalf("zero installation: %v %v", b, e)
		}
	}
	for _, b := range []*CheckedBundle{nil, {}} {
		if b.Valid() || b.SourceBytes() != nil || b.WasmBytes() != nil || b.ARM64Bytes() != nil || b.RV64Bytes() != nil {
			t.Fatal("zero bundle authority")
		}
	}
	var b CheckedBundle
	if err := json.Unmarshal([]byte(`{"valid":true,"schema":"oak.checked-bundle.v1"}`), &b); err == nil || b.Valid() {
		t.Fatal("JSON restored authority")
	}
}
func TestSnapshotsAndDriver(t *testing.T) {
	input := fixture(t)
	in, err := requestInput(input[0], input[1], input[2], input[3])
	if err != nil {
		t.Fatal(err)
	}
	for n := range input {
		old := in[n][0]
		input[n][0] ^= 1
		if in[n][0] != old {
			t.Fatal("snapshot aliases caller")
		}
	}
	d, err := driver(in)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Contains(d, in[0]) || bytes.Count(d, []byte("#oak_checked_bundle_audit")) != 1 {
		t.Fatal("raw source interpolation or wrong audit")
	}
	tooBig := make([]byte, MaxSourceBytes+1)
	if _, err = requestInput(tooBig, []byte{1}, []byte{1}, []byte{1}); !errors.Is(err, ErrBounds) {
		t.Fatal("source bound")
	}
	max := [4][]byte{bytes.Repeat([]byte{255}, MaxSourceBytes), bytes.Repeat([]byte{255}, MaxWasmBytes), bytes.Repeat([]byte{255}, MaxObjectBytes), bytes.Repeat([]byte{255}, MaxObjectBytes)}
	if d, e := driver(max); e != nil || len(d) > MaxDriverBytes {
		t.Fatalf("max driver: %d %v", len(d), e)
	}
}
func TestInstallRefusesUntrustedArchive(t *testing.T) {
	for _, data := range [][]byte{nil, []byte("Lean (version 4.33.1)\n"), []byte(`{"sha256":"trusted"}`)} {
		file := filepath.Join(t.TempDir(), "archive")
		if err := os.WriteFile(file, data, 0600); err != nil {
			t.Fatal(err)
		}
		if i, e := Install(context.Background(), file); i != nil || e == nil {
			t.Fatal("untrusted archive accepted")
		}
	}
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if i, e := Install(ctx, "missing"); i != nil || !errors.Is(e, context.Canceled) {
		t.Fatal("canceled setup")
	}
}
func TestRealKernelAdmission(t *testing.T) {
	archive := os.Getenv("OAK_BITWISECHECK_LEAN_ARCHIVE")
	if archive == "" {
		if os.Getenv("OAK_REQUIRE_BITWISECHECK") == "1" {
			t.Fatal("OAK_BITWISECHECK_LEAN_ARCHIVE required")
		}
		t.Skip("set OAK_BITWISECHECK_LEAN_ARCHIVE for real pinned-runtime admission")
	}
	// Poison ambient executable/import/loader configuration. The same mandatory
	// real positive admission below must still succeed through private custody.
	poison := t.TempDir()
	if e := os.MkdirAll(filepath.Join(poison, "Oak"), 0700); e != nil {
		t.Fatal(e)
	}
	for _, name := range []string{"CheckedBundleAudit.olean", "BitwiseSourceObjectParity.olean"} {
		if e := os.WriteFile(filepath.Join(poison, "Oak", name), []byte("caller-authored fake olean"), 0600); e != nil {
			t.Fatal(e)
		}
	}
	for _, key := range []string{"LEAN_PATH", "LEAN_SYSROOT", "OAK_LEAN_DIR", "ELAN_TOOLCHAIN", "PATH", "HOME", "TMPDIR"} {
		t.Setenv(key, poison)
	}
	t.Setenv("LD_PRELOAD", filepath.Join(poison, "untrusted-loader.so"))
	start := time.Now()
	inst, err := Install(context.Background(), archive)
	if err != nil {
		t.Fatal(err)
	}
	defer inst.Close()
	t.Logf("installed in %s", time.Since(start))
	original := fixture(t)
	in := fixture(t)
	b, err := inst.CheckBundle(context.Background(), in[0], in[1], in[2], in[3])
	if err != nil {
		t.Fatal(err)
	}
	if !b.Valid() {
		t.Fatal("real admission invalid")
	}
	t.Logf("admitted in %s", time.Since(start))
	for n := range in {
		in[n][0] ^= 1
	}
	getters := []func() []byte{b.SourceBytes, b.WasmBytes, b.ARM64Bytes, b.RV64Bytes}
	for n, get := range getters {
		if !bytes.Equal(get(), original[n]) {
			t.Fatal("input mutation changed bundle")
		}
		copy := get()
		copy[0] ^= 1
		if !bytes.Equal(get(), original[n]) {
			t.Fatal("getter aliases")
		}
	}
	receipt := b.Receipt()
	receipt.Roots[1].Axioms[0] = "sorryAx"
	receipt.Assumptions[0] = "changed"
	if b.Receipt().Assumptions[0] == "changed" || b.Receipt().Roots[1].Axioms[0] == "sorryAx" {
		t.Fatal("receipt aliases")
	}
	raw, err := json.Marshal(b)
	if err != nil {
		t.Fatal(err)
	}
	var replay CheckedBundle
	if json.Unmarshal(raw, &replay) == nil || replay.Valid() {
		t.Fatal("receipt replay")
	}
	for n := range original {
		bad := fixture(t)
		bad[n] = append(bad[n], 0)
		if got, e := inst.CheckBundle(context.Background(), bad[0], bad[1], bad[2], bad[3]); got != nil || e == nil {
			t.Fatalf("bad input %d admitted", n)
		} else {
			var exit *exec.ExitError
			if !errors.As(e, &exit) || exit.ExitCode() != 1 || !strings.Contains(e.Error(), "checked bundle refused: Oak.CheckedBundleRequest.admitted depends on forbidden axiom sorryAx") {
				t.Fatalf("bad input %d did not reach the expected fail-closed audit: %v", n, e)
			}
		}
		if e := inst.state.proveRefusal(context.Background(), bad); e != nil {
			t.Fatalf("bad input %d lacks a successful independent kernel refusal proof: %v", n, e)
		}

	}
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	if got, e := inst.CheckBundle(ctx, original[0], original[1], original[2], original[3]); got != nil || !errors.Is(e, context.Canceled) {
		t.Fatal("canceled request")
	}
	var wg sync.WaitGroup
	for n := 0; n < 2; n++ {
		source := original[0]
		if n == 1 {
			source = []byte("bitwise: (left: u32, right: u32): u32 = left & right\n")
		}
		wg.Add(1)
		go func(source []byte) {
			defer wg.Done()
			b, e := inst.CheckBundle(context.Background(), source, original[1], original[2], original[3])
			if e != nil || !b.Valid() {
				t.Errorf("concurrent request: %v", e)
				return
			}
			if !bytes.Equal(b.SourceBytes(), source) {
				t.Error("concurrent requests mixed owned source snapshots")
			}
		}(source)
	}
	wg.Wait()

	t.Run("ValidRecordThenFailure", func(t *testing.T) {
		generated, e := driver(original)
		if e != nil {
			t.Fatal(e)
		}
		generated = append(generated, []byte("example : False := by trivial\n")...)
		out, e := inst.state.runRequest(context.Background(), generated)
		var exit *exec.ExitError
		if out != nil || e == nil || !errors.As(e, &exit) || exit.ExitCode() != 1 || !strings.Contains(e.Error(), Schema) {
			t.Fatalf("expected an audited record followed by nonzero exit, got %q %v", out, e)
		}
	})
	t.Run("CanceledQueue", func(t *testing.T) {
		inst.state.gate <- struct{}{}
		defer func() { <-inst.state.gate }()
		ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
		defer cancel()
		got, e := inst.CheckBundle(ctx, original[0], original[1], original[2], original[3])
		if got != nil || !errors.Is(e, context.DeadlineExceeded) {
			t.Fatalf("queued cancellation: %v", e)
		}
	})
	t.Run("CloseActiveRequest", func(t *testing.T) {
		result := make(chan error, 1)
		go func() {
			got, e := inst.CheckBundle(context.Background(), original[0], original[1], original[2], original[3])
			if got != nil {
				result <- errors.New("Close admitted active request")
				return
			}
			result <- e
		}()
		pid := waitLeanChild(t, inst.state.lean)

		if e := inst.Close(); e != nil {
			t.Fatal(e)
		}
		if e := <-result; !errors.Is(e, context.Canceled) && !errors.Is(e, ErrInvalidInstallation) {
			t.Fatalf("Close request result: %v", e)
		}
		if runningLean(pid, inst.state.lean) {
			t.Fatal("Lean child survived Close")
		}
		if _, e := os.Stat(inst.state.root); !os.IsNotExist(e) {
			t.Fatalf("owned root survived Close: %v", e)
		}
	})
	if err = inst.Close(); err != nil {
		t.Fatal(err)
	}
	if inst.Valid() {
		t.Fatal("closed valid")
	}
	if got, e := inst.CheckBundle(context.Background(), original[0], original[1], original[2], original[3]); got != nil || !errors.Is(e, ErrInvalidInstallation) {
		t.Fatal("closed request")
	}
	if !b.Valid() {
		t.Fatal("Close invalidated completed historical admission")
	}
}

// Real Linux process observation only. This cannot inject a runner, forge an
// installation, or manufacture a successful bundle.
func runningLean(pid, program string) bool {
	cmdline, e := os.ReadFile(filepath.Join("/proc", pid, "cmdline"))
	if e != nil {
		return false
	}
	executable, _, _ := bytes.Cut(cmdline, []byte{0})
	return string(executable) == program
}
func waitLeanChild(t *testing.T, program string) string {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for time.Now().Before(deadline) {
		processes, e := os.ReadDir("/proc")
		if e != nil {
			t.Fatal(e)
		}
		for _, p := range processes {
			if _, e := strconv.Atoi(p.Name()); e == nil && runningLean(p.Name(), program) {
				return p.Name()
			}
		}
		time.Sleep(time.Millisecond)
	}
	t.Fatal("pinned Lean child did not start")
	return ""
}
