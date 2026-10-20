package bitwisecheck

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
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

func imageFixture(t *testing.T) [4][]byte {
	t.Helper()
	in, e := imageSelfTestInput()
	if e != nil {
		t.Fatal(e)
	}
	return in
}
func TestImageZeroAuthority(t *testing.T) {
	typ := reflect.TypeFor[CheckedImageBundle]()
	for _, n := range []string{"source", "wasm", "arm", "rv"} {
		f, ok := typ.FieldByName(n)
		if !ok || f.Type.Kind() != reflect.String {
			t.Fatalf("mutable %s storage", n)
		}
	}
	for _, i := range []*ImageInstallation{nil, {}} {
		if i.Valid() {
			t.Fatal("invalid installation valid")
		}
		b, e := i.CheckImageBundle(context.Background(), nil, nil, nil, nil)
		if b != nil || !errors.Is(e, ErrInvalidInstallation) {
			t.Fatal("zero installation admitted")
		}
		if !errors.Is(i.Close(), ErrInvalidInstallation) {
			t.Fatal("zero close")
		}
	}
	for _, b := range []*CheckedImageBundle{nil, {}} {
		if b.Valid() || b.SourceBytes() != nil || b.WasmBytes() != nil || b.ARM64ImageBytes() != nil || b.RV64ImageBytes() != nil {
			t.Fatal("zero bundle valid")
		}
		if _, e := b.MarshalJSON(); !errors.Is(e, ErrInvalidBundle) {
			t.Fatal("zero marshalled")
		}
	}
	var b CheckedImageBundle
	if e := json.Unmarshal([]byte(`{"schema":"oak.checked-image-bundle.v1","valid":true}`), &b); e == nil || b.Valid() {
		t.Fatal("receipt restored authority")
	}
	if imageInstallationSeal == installationSeal || imageBundleSeal == bundleSeal {
		t.Fatal("shared capability seal")
	}
}
func TestImageClosedInstallationProfile(t *testing.T) {
	st, err := installRuntime(context.Background(), "", installationProfile{kind: installationKind(255)})
	if st != nil || err == nil || !strings.Contains(err.Error(), "unknown private installation profile") {
		t.Fatalf("unknown profile did not fail closed: %v", err)
	}
	for _, profile := range []installationProfile{{kind: objectInstallation}, {kind: imageInstallation, authority: installationSeal}, {kind: objectInstallation, authority: imageInstallationSeal}} {
		if st, err := installRuntime(context.Background(), "", profile); st != nil || err == nil || !strings.Contains(err.Error(), "incomplete or mismatched private installation profile") {
			t.Fatalf("incomplete profile did not fail closed: %v", err)
		}
	}
}
func TestImageSnapshotAndRenderer(t *testing.T) {
	caller := imageFixture(t)
	owned, e := imageRequestInput(caller[0], caller[1], caller[2], caller[3])
	if e != nil {
		t.Fatal(e)
	}
	for n := range caller {
		caller[n][0] ^= 1
		if owned[n][0] == caller[n][0] {
			t.Fatal("input alias")
		}
	}
	driver, e := imageDriver(owned)
	if e != nil {
		t.Fatal(e)
	}
	if bytes.Contains(driver, owned[0]) || bytes.Count(driver, []byte("#oak_source_image_parity_audit")) != 1 {
		t.Fatal("raw interpolation/audit inventory")
	}
	for _, in := range owned[2:] {
		header, suffix, e := imageParts(in)
		if e != nil {
			t.Fatal(e)
		}
		roundtrip := append(append(append([]byte{}, header...), make([]byte, 3976)...), suffix...)
		if !bytes.Equal(roundtrip, in) {
			t.Fatal("compression changed bytes")
		}
	}
	for _, at := range []int{120, 4095} {
		bad := imageFixture(t)
		bad[2][at] = 1
		if _, e := imageDriver(bad); e == nil {
			t.Fatal("nonzero gap normalized")
		}
	}
	for n, limit := range []int{MaxSourceBytes, MaxWasmBytes, MaxImageBytes, MaxImageBytes} {
		bad := imageFixture(t)
		bad[n] = make([]byte, limit+1)
		if _, e := imageRequestInput(bad[0], bad[1], bad[2], bad[3]); !errors.Is(e, ErrBounds) {
			t.Fatalf("bound %d", n)
		}
	}
	t.Logf("ordinary driver bytes=%d", len(driver))
}
func imageMaxFixture(t *testing.T) [4][]byte {
	t.Helper()
	var in [4][]byte
	for n, name := range []string{"source", "wasm", "arm", "rv"} {
		b, e := os.ReadFile(filepath.Join("testdata", "image-max-"+name+".fixture"))
		if e != nil {
			t.Fatal(e)
		}
		in[n] = b
	}
	return in
}

// Resource observations are test-only. They cannot inject runners or grant
// authority. Sampling records this installation's actual Lean process RSS.
func measuredImageRequest(t *testing.T, i *ImageInstallation, in [4][]byte) (*CheckedImageBundle, error) {
	t.Helper()
	done := make(chan struct{})
	var wg sync.WaitGroup
	var peak int64
	wg.Add(1)
	go func() {
		defer wg.Done()
		ticker := time.NewTicker(10 * time.Millisecond)
		defer ticker.Stop()
		for {
			select {
			case <-done:
				return
			case <-ticker.C:
				entries, _ := os.ReadDir("/proc")
				for _, entry := range entries {
					if !runningLean(entry.Name(), i.state.lean) {
						continue
					}
					raw, _ := os.ReadFile(filepath.Join("/proc", entry.Name(), "status"))
					for _, line := range strings.Split(string(raw), "\n") {
						if strings.HasPrefix(line, "VmRSS:") {
							fields := strings.Fields(line)
							if len(fields) > 1 {
								rss, _ := strconv.ParseInt(fields[1], 10, 64)
								if rss > peak {
									peak = rss
								}
							}
						}
					}
				}
			}
		}
	}()
	start := time.Now()
	b, err := i.CheckImageBundle(context.Background(), in[0], in[1], in[2], in[3])
	close(done)
	wg.Wait()
	generated, e := imageDriver(in)
	if e != nil {
		t.Fatal(e)
	}
	t.Logf("inputs=%d/%d/%d/%d driver=%d elapsed=%s peak_child_rss_kib=%d", len(in[0]), len(in[1]), len(in[2]), len(in[3]), len(generated), time.Since(start), peak)
	return b, err
}
func expectImageAuditRefusal(t *testing.T, i *ImageInstallation, driver []byte, marker string) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), RequestTimeout)
	defer cancel()
	out, e := i.state.runRequest(ctx, driver)
	var exit *exec.ExitError
	if out != nil || !errors.As(e, &exit) || exit.ExitCode() != 1 || !strings.Contains(e.Error(), "source image parity refused:") || !strings.Contains(e.Error(), marker) {
		t.Fatalf("expected exact new-auditor refusal %q: %v", marker, e)
	}
}
func TestImagePinnedRuntime(t *testing.T) {
	archive := os.Getenv("OAK_BITWISECHECK_LEAN_ARCHIVE")
	if archive == "" {
		if os.Getenv("OAK_REQUIRE_BITWISE_IMAGECHECK") == "1" {
			t.Fatal("pinned archive is required")
		}
		t.Skip("set OAK_BITWISECHECK_LEAN_ARCHIVE for real pinned image runtime")
	}

	t.Run("CanceledSetup", func(t *testing.T) {
		before, _ := filepath.Glob("/tmp/oak-bitwisecheck-*")
		ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
		defer cancel()
		got, e := InstallImages(ctx, archive)
		if got != nil || !errors.Is(e, context.DeadlineExceeded) {
			if got != nil {
				_ = got.Close()
			}
			t.Fatalf("canceled setup %v", e)
		}
		after, _ := filepath.Glob("/tmp/oak-bitwisecheck-*")
		if !reflect.DeepEqual(before, after) {
			t.Fatal("canceled setup leaked owned files")
		}
	})
	poison := t.TempDir()
	for _, key := range []string{"LEAN_PATH", "LEAN_SYSROOT", "OAK_LEAN_DIR", "ELAN_TOOLCHAIN", "PATH", "HOME", "TMPDIR"} {
		t.Setenv(key, poison)
	}
	t.Setenv("LD_PRELOAD", filepath.Join(poison, "untrusted-loader.so"))
	start := time.Now()
	inst, err := InstallImages(context.Background(), archive)
	if err != nil {
		t.Fatal(err)
	}
	defer inst.Close()
	t.Logf("fresh image installation and actual positive/refusal controls: %s", time.Since(start))
	in := imageFixture(t)
	start = time.Now()
	b, err := measuredImageRequest(t, inst, in)
	if err != nil {
		t.Fatal(err)
	}
	if !b.Valid() {
		t.Fatal("real image admission invalid")
	}
	t.Logf("actual paired image admission: %s", time.Since(start))
	original := imageFixture(t)
	for n := range in {
		in[n][0] ^= 1
	}
	for n, get := range []func() []byte{b.SourceBytes, b.WasmBytes, b.ARM64ImageBytes, b.RV64ImageBytes} {
		if !bytes.Equal(get(), original[n]) {
			t.Fatal("input mutation changed admission")
		}
		copy := get()
		copy[0] ^= 1
		if !bytes.Equal(get(), original[n]) {
			t.Fatal("getter alias")
		}
	}
	r := b.Receipt()
	if r.Schema != ImageSchema || r.Profile != ImageProfile || r.Targets[1].ELFEntry != 65536 || r.Targets[1].FunctionAddress != 65548 || r.Targets[2].FunctionAddress != 65552 {
		t.Fatal("wrong receipt profile")
	}
	if len(r.Roots[1].Axioms) == 0 {
		t.Fatal("unexpected empty contract closure")
	}
	r.Roots[1].Axioms[0] = "sorryAx"
	r.Assumptions[0] = "changed"
	r.Guarantees[0] = "changed"
	if b.Receipt().Roots[1].Axioms[0] == "sorryAx" || b.Receipt().Assumptions[0] == "changed" || b.Receipt().Guarantees[0] == "changed" {
		t.Fatal("receipt alias")
	}

	t.Run("CrossProfileInstallationSeal", func(t *testing.T) {
		legacy := (*Installation)(inst)
		if legacy.Valid() {
			t.Fatal("converted image handle became object authority")
		}
		if got, e := legacy.CheckBundle(context.Background(), original[0], original[1], original[2], original[3]); got != nil || !errors.Is(e, ErrInvalidInstallation) {
			t.Fatal("cross-profile object check")
		}
		if !errors.Is(legacy.Close(), ErrInvalidInstallation) || !inst.Valid() {
			t.Fatal("converted handle closed image state")
		}
	})
	copied := *inst
	t.Run("CanceledBeforeRequest", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())
		cancel()
		if got, e := inst.CheckImageBundle(ctx, original[0], original[1], original[2], original[3]); got != nil || !errors.Is(e, context.Canceled) {
			t.Fatalf("pre-canceled request %v", e)
		}
	})
	t.Run("MaximumNameAndSource", func(t *testing.T) {
		maximum := imageMaxFixture(t)
		if len(maximum[0]) != 2048 || len(maximum[2]) != 4896 || len(maximum[3]) != 4928 {
			t.Fatal("wrong maximum fixture")
		}
		got, e := measuredImageRequest(t, inst, maximum)
		if e != nil {
			t.Fatal(e)
		}
		if !got.Valid() || len(got.Receipt().Declaration.Name) != 256 {
			t.Fatal("maximum authority")
		}
		// Request the actual auditor output independently for exact protocol length.
		generated, e := imageDriver(maximum)
		if e != nil {
			t.Fatal(e)
		}
		ctx, cancel := context.WithTimeout(context.Background(), RequestTimeout)
		defer cancel()
		out, e := inst.state.runRequest(ctx, generated)
		if e != nil {
			t.Fatal(e)
		}
		if _, e = validateImageProtocol(out, maximum); e != nil {
			t.Fatal(e)
		}
		t.Logf("actual maximum paired auditor output bytes=%d", len(out))
	})
	t.Run("ActualBodyMutation", func(t *testing.T) {
		bad := imageFixture(t)
		bad[2][4108] ^= 1
		generated, e := imageDriver(bad)
		if e != nil {
			t.Fatal(e)
		}
		expectImageAuditRefusal(t, inst, generated, "depends on forbidden axiom sorryAx")
		if got, e := inst.CheckImageBundle(context.Background(), bad[0], bad[1], bad[2], bad[3]); got != nil || e == nil {
			t.Fatal("mutation minted authority")
		}
	})
	t.Run("ActualSuccessfulRefusalProof", func(t *testing.T) {
		bad := imageFixture(t)
		bad[1] = append(bad[1], 0)
		d, e := imageRefusalDriver(bad)
		if e != nil {
			t.Fatal(e)
		}
		ctx, cancel := context.WithTimeout(context.Background(), RequestTimeout)
		defer cancel()
		out, e := inst.state.runRequest(ctx, d)
		if e != nil || len(out) != 0 {
			t.Fatalf("negative control must succeed silently: %q %v", out, e)
		}
	})
	t.Run("WrongExactRootType", func(t *testing.T) {
		d, e := imageDriver(original)
		if e != nil {
			t.Fatal(e)
		}
		old := "theorem all_inputs : type_of% (accepted_all_input_success admitted) := accepted_all_input_success admitted"
		d = bytes.Replace(d, []byte(old), []byte("theorem all_inputs : True := True.intro"), 1)
		expectImageAuditRefusal(t, inst, d, "has the wrong exact type or value")
	})

	t.Run("InvalidCurrentDependencyBody", func(t *testing.T) {
		d, e := imageDriver(original)
		if e != nil {
			t.Fatal(e)
		}
		bad := `open Lean Elab Command
elab "invalidImageDependencyForRegression" : command => do
  liftCoreM <| Lean.addDecl (.thmDecl {
    name := ` + "`" + `Oak.TransientUnchecked.falseHelper
    levelParams := []
    type := mkConst ` + "``" + `False
    value := mkConst ` + "``" + `True.intro })
set_option debug.skipKernelTC true in
invalidImageDependencyForRegression
`
		d = bytes.Replace(d, []byte("namespace Oak.SourceImageParityRequest\n"), []byte(bad+"namespace Oak.SourceImageParityRequest\n"), 1)
		start := bytes.Index(d, []byte("theorem admitted :"))
		end := bytes.Index(d, []byte("theorem binding :"))
		if start < 0 || end < start {
			t.Fatal("admission template boundary")
		}
		forged := []byte("theorem admitted : Oak.BitwiseSourceImageParity.check source wasm arm rv = some declaration := False.elim Oak.TransientUnchecked.falseHelper\n")
		altered := append(append(append([]byte{}, d[:start]...), forged...), d[end:]...)
		expectImageAuditRefusal(t, inst, altered, "has the wrong exact type or value")
	})
	for _, target := range []string{"arm", "rv"} {
		t.Run("DropContract/"+target, func(t *testing.T) {
			d, e := imageDriver(original)
			if e != nil {
				t.Fatal(e)
			}
			weak, e := os.ReadFile(filepath.Join("testdata", "image-drop-"+target+".lean"))
			if e != nil {
				t.Fatal(e)
			}
			old := []byte("theorem all_inputs : type_of% (accepted_all_input_success admitted) := accepted_all_input_success admitted\n")
			if bytes.Count(d, old) != 1 {
				t.Fatal("root template changed")
			}
			d = bytes.Replace(d, old, weak, 1)
			expectImageAuditRefusal(t, inst, d, "has the wrong exact type or value")
		})
	}

	t.Run("ValidRecordThenFailure", func(t *testing.T) {
		d, e := imageDriver(original)
		if e != nil {
			t.Fatal(e)
		}
		d = append(d, []byte("#check nonexistent_after_success\n")...)
		ctx, cancel := context.WithTimeout(context.Background(), RequestTimeout)
		defer cancel()
		out, e := inst.state.runRequest(ctx, d)
		var exit *exec.ExitError
		if out != nil || !errors.As(e, &exit) || exit.ExitCode() != 1 || !strings.Contains(e.Error(), imageAuditSchema) {
			t.Fatalf("record before failure escaped: %q %v", out, e)
		}
	})
	t.Run("CanceledInstallationQueue", func(t *testing.T) {
		inst.state.gate <- struct{}{}
		defer func() { <-inst.state.gate }()
		ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
		defer cancel()
		got, e := inst.CheckImageBundle(ctx, original[0], original[1], original[2], original[3])
		if got != nil || !errors.Is(e, context.DeadlineExceeded) {
			t.Fatalf("queue cancellation %v", e)
		}
	})
	t.Run("CanceledGlobalQueue", func(t *testing.T) {
		leanProcessGate <- struct{}{}
		defer func() { <-leanProcessGate }()
		ctx, cancel := context.WithTimeout(context.Background(), 20*time.Millisecond)
		defer cancel()
		got, e := inst.CheckImageBundle(ctx, original[0], original[1], original[2], original[3])
		if got != nil || !errors.Is(e, context.DeadlineExceeded) {
			t.Fatalf("global queue cancellation %v", e)
		}
	})

	t.Run("CanceledActiveRequest", func(t *testing.T) {
		ctx, cancel := context.WithCancel(context.Background())
		defer cancel()
		result := make(chan error, 1)
		go func() {
			got, e := inst.CheckImageBundle(ctx, original[0], original[1], original[2], original[3])
			if got != nil {
				result <- fmt.Errorf("canceled request admitted")
			} else {
				result <- e
			}
		}()
		pid := waitLeanChild(t, inst.state.lean)
		cancel()
		if e := <-result; !errors.Is(e, context.Canceled) {
			t.Fatalf("active cancellation %v", e)
		}
		if runningLean(pid, inst.state.lean) || !inst.Valid() {
			t.Fatal("cancellation did not reap or closed installation")
		}
	})
	t.Run("CloseActiveRequest", func(t *testing.T) {
		result := make(chan error, 1)
		go func() {
			got, e := inst.CheckImageBundle(context.Background(), original[0], original[1], original[2], original[3])
			if got != nil {
				result <- fmt.Errorf("Close admitted active request")
			} else {
				result <- e
			}
		}()
		pid := waitLeanChild(t, inst.state.lean)
		if e := inst.Close(); e != nil {
			t.Fatal(e)
		}
		if e := <-result; !errors.Is(e, context.Canceled) && !errors.Is(e, ErrInvalidInstallation) {
			t.Fatalf("Close result %v", e)
		}
		if runningLean(pid, inst.state.lean) {
			t.Fatal("child survived Close")
		}
		if _, e := os.Stat(inst.state.root); !os.IsNotExist(e) {
			t.Fatal("private files survived Close")
		}
	})
	if e := inst.Close(); e != nil {
		t.Fatal(e)
	}
	t.Run("CopiedInstallationClose", func(t *testing.T) {
		if copied.Valid() {
			t.Fatal("copied wrapper survived Close")
		}
		if e := copied.Close(); e != nil {
			t.Fatal(e)
		}
	})
	if inst.Valid() || !b.Valid() {
		t.Fatal("closed state/historical authority")
	}
}
