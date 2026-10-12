package compiler

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"sync"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/target"
)

func verificationCompilation(supplied bool, arch string) Compilation {
	comp := New().WithSource("options.oak", "identity: (x: u32): u32 = x\n").
		WithTarget(target.Target{OS: target.OSLinux, Arch: arch}).WithVerifyFresh()
	if supplied {
		return comp.WithAsmUnit("identity.arm64.oakasm", "identity: (x: u32): u32 = {\n bind w0 = x\n ret\n}\n")
	}
	return comp.WithNativeBodies()
}

func TestVerificationOptionsCheckCapturesBeforeRewritesAndRecapturesOnReuse(t *testing.T) {
	t.Setenv("OAK_VERIFY_OFF", "")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	for _, test := range []struct {
		name     string
		supplied bool
		arch     string
	}{{"supplied", true, target.ArchArm64}, {"generated-arm64", false, target.ArchArm64}, {"generated-rv64", false, target.ArchRiscv64}} {
		t.Run(test.name, func(t *testing.T) {
			t.Setenv("OAK_VERIFY_ONLY", "other")
			comp := verificationCompilation(test.supplied, test.arch).WithSyntaxRewrite(func(*SyntaxTree) error {
				return os.Setenv("OAK_VERIFY_ONLY", "")
			})
			first, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			if got := first.NativeVerdicts["identity"]; got.Kind != asm.VerdictTrusted || got.Message != "skipped under OAK_VERIFY_ONLY" {
				t.Fatalf("entry snapshot lost at verification: %+v", got)
			}
			second, err := comp.Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			if got := second.NativeVerdicts["identity"]; got.Kind != asm.VerdictProven {
				t.Fatalf("reused compilation retained prior captured settings: %+v", got)
			}
			if comp.verificationOptionsSupplied || comp.verificationOptions.SelectionActive() {
				t.Fatal("check persisted captured settings into reusable compilation")
			}
		})
	}
}

func TestVerificationOptionsExplicitZeroOverridesAmbient(t *testing.T) {
	t.Setenv("OAK_VERIFY_OFF", "bounded,onesided,components,selfprune")
	t.Setenv("OAK_VERIFY_BUDGET", "high")
	t.Setenv("OAK_VERIFY_ONLY", "other")
	base := verificationCompilation(true, target.ArchArm64)
	explicit := base.WithVerificationOptions(asm.VerificationOptions{})
	if base.verificationOptionsSupplied || !explicit.verificationOptionsSupplied {
		t.Fatal("WithVerificationOptions did not preserve copy-on-write override ownership")
	}
	for i := 0; i < 2; i++ {
		model, err := explicit.Check().Get()
		if err != nil {
			t.Fatal(err)
		}
		if model.NativeVerdicts["identity"].Kind != asm.VerdictProven {
			t.Fatal(model.NativeVerdicts)
		}
	}
	if explicit.captureVerificationRun().options.CacheIdentity() != (asm.VerificationOptions{}).CacheIdentity() {
		t.Fatal("explicit default was replaced by ambient options")
	}
}

func TestVerificationOptionsConcurrentCompilations(t *testing.T) {
	// No environment mutation: each goroutine owns its compiler, syntax tree,
	// proof state and explicit settings. Shared physical admission stays global.
	var wg sync.WaitGroup
	for _, options := range []asm.VerificationOptions{{}, asm.NewVerificationOptions("components", "base", "other")} {
		wg.Add(1)
		go func(options asm.VerificationOptions) {
			defer wg.Done()
			comp := verificationCompilation(true, target.ArchArm64).WithVerificationOptions(options)
			for i := 0; i < 3; i++ {
				model, err := comp.Check().Get()
				if err != nil {
					t.Error(err)
					return
				}
				got := model.NativeVerdicts["identity"]
				if options.SelectionActive() {
					if got.Kind != asm.VerdictTrusted || got.Message != "skipped under OAK_VERIFY_ONLY" {
						t.Errorf("selection contaminated: %+v", got)
					}
				} else if got.Kind != asm.VerdictProven && !got.TransientResourceExhausted {
					t.Errorf("default contaminated: %+v", got)
				}
			}
		}(options)
	}
	wg.Wait()
}

func verificationCacheFixture(t *testing.T) (*asm.Function, *ast.FunctionStatement, map[string]*ast.FunctionStatement) {
	t.Helper()
	p := parser.New(layout.New(scanner.New("identity: (x: u32): u32 = x\n")))
	root := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := root.Statements[0].(*ast.FunctionStatement)
	return &asm.Function{Name: "identity", Arch: asm.ArchArm64, Signature: fn}, fn, map[string]*ast.FunctionStatement{"identity": fn}
}

func TestVerificationOptionsCacheIdentityAndCapturedPolicy(t *testing.T) {
	machine, source, functions := verificationCacheFixture(t)
	t.Setenv("OAK_VERIFY_OFF", "bounded")
	t.Setenv("OAK_VERIFY_BUDGET", "high")
	t.Setenv("OAK_VERIFY_ONLY", "")
	t.Setenv("OAK_VERIFY_CACHE", "1")
	comp := New()
	run := comp.captureVerificationRun()
	key := verdictCacheKey(machine, source, functions, "", run.options)
	t.Setenv("OAK_VERIFY_OFF", "components")
	t.Setenv("OAK_VERIFY_BUDGET", "base")
	t.Setenv("OAK_VERIFY_ONLY", "other")
	t.Setenv("OAK_VERIFY_CACHE", "0")
	if run.cacheDir == "" || verdictCacheKey(machine, source, functions, "", run.options) != key {
		t.Fatal("ambient changes redirected a captured lookup/store")
	}
	if next := comp.captureVerificationRun(); next.cacheDir != "" || next.options.CacheIdentity() == run.options.CacheIdentity() {
		t.Fatal("next capture did not observe changed settings")
	}
	seen := map[string]bool{}
	for _, options := range []asm.VerificationOptions{{}, asm.NewVerificationOptions("bounded", "", ""), asm.NewVerificationOptions("", "high", ""), asm.NewVerificationOptions("", "", "other")} {
		k := verdictCacheKey(machine, source, functions, "", options)
		if seen[k] {
			t.Fatal("different option snapshots collided")
		}
		seen[k] = true
	}
	if verdictCacheNamespace == "verdict-cache-5-truncated-parameter-extension" {
		t.Fatal("old cache namespace retained")
	}
	// A proof stored under B must not be restored under A.
	dir := t.TempDir()
	a := verdictCacheKey(machine, source, functions, "", asm.VerificationOptions{})
	b := verdictCacheKey(machine, source, functions, "", asm.NewVerificationOptions("bounded", "", ""))
	storeVerdict(dir, b, asm.Verdict{Kind: asm.VerdictProven, Message: "B only"})
	if got, hit := cachedVerdict(dir, a, functions); hit {
		t.Fatalf("foreign options restored: %+v", got)
	}
}

func TestVerificationOptionsCacheBypassesReadAndStore(t *testing.T) {
	for _, test := range []struct {
		name, cache string
		fresh       bool
		options     asm.VerificationOptions
	}{{name: "selection", options: asm.NewVerificationOptions("", "", "other")}, {name: "cache-off", cache: "0"}, {name: "fresh", fresh: true}} {
		t.Run(test.name, func(t *testing.T) {
			t.Setenv("TMPDIR", t.TempDir())
			_, source, functions := verificationCacheFixture(t)
			run := newVerificationRun(test.options, test.cache, test.fresh)
			if run.cacheDir != "" {
				t.Fatal("policy did not disable cache")
			}
			verified, cached := 0, 0
			d := &nativeDriver{source: source, functions: functions, verificationOptions: run.options,
				cacheDir: run.cacheDir, verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &cached}
			candidate := opt.Identity(nativegen.PlainLane(nativegen.Lane{Arch: asm.ArchArm64}))
			if err := d.Materialize(candidate); err != nil {
				t.Fatal(err)
			}
			machine := candidate.Body.(*asm.Function)
			key := verdictCacheKey(machine, source, functions, "", run.options)
			// Seed a would-be cache hit. The disabled driver must ignore it and
			// leave its contents untouched, including after a selection skip.
			dir := filepath.Join(os.TempDir(), "oak-verify-cache")
			storeVerdict(dir, key, asm.Verdict{Kind: asm.VerdictProven, Message: "sentinel"})
			path := filepath.Join(dir, key+".verdict")
			before, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			got := d.Validate(candidate)
			if got.Cached || cached != 0 || verified != 1 || got.Message == "sentinel" {
				t.Fatalf("disabled cache read: %+v", got)
			}
			if test.options.SelectionActive() && got.Outcome != opt.Trusted {
				t.Fatalf("skip became proof: %+v", got)
			}
			after, err := os.ReadFile(path)
			if err != nil || string(after) != string(before) {
				t.Fatal("disabled cache store changed entry", err)
			}
		})
	}
}

func TestVerificationOptionsCapturedNativeLookupAndStore(t *testing.T) {
	t.Setenv("TMPDIR", t.TempDir())
	t.Setenv("OAK_VERIFY_OFF", "")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	t.Setenv("OAK_VERIFY_ONLY", "")
	t.Setenv("OAK_VERIFY_CACHE", "1")
	run := New().captureVerificationRun()
	_, source, functions := verificationCacheFixture(t)
	verified, cached := 0, 0
	d := &nativeDriver{source: source, functions: functions, verificationOptions: run.options,
		cacheDir: run.cacheDir, verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &cached}
	candidate := opt.Identity(nativegen.PlainLane(nativegen.Lane{Arch: asm.ArchArm64}))
	if err := d.Materialize(candidate); err != nil {
		t.Fatal(err)
	}
	machine := candidate.Body.(*asm.Function)
	key := verdictCacheKey(machine, source, functions, "", run.options)
	// These edits would disable or redirect the original ambient implementation.
	t.Setenv("OAK_VERIFY_OFF", "bounded")
	t.Setenv("OAK_VERIFY_BUDGET", "high")
	t.Setenv("OAK_VERIFY_ONLY", "other")
	t.Setenv("OAK_VERIFY_CACHE", "0")
	first := d.Validate(candidate)
	if first.Outcome != opt.Proven || first.Cached {
		t.Fatalf("capture lost on fresh validation: %+v", first)
	}
	if stored, hit := cachedVerdict(run.cacheDir, key, functions); !hit || stored.Kind != asm.VerdictProven {
		t.Fatalf("store did not use the lookup snapshot/key: %+v %v", stored, hit)
	}
	second := d.Validate(candidate)
	if !second.Cached || second.Outcome != opt.Proven || cached != 1 || verified != 2 {
		t.Fatalf("captured policy lost on lookup: %+v, cached=%d verified=%d", second, cached, verified)
	}
}

// This fixture has no globals, composites, rewritten body or reachable calls,
// so the pinned v5 encoding consists exactly of the fields reproduced here.
func TestVerificationOptionsRejectsOldNamespaceEntry(t *testing.T) {
	machine, source, functions := verificationCacheFixture(t)
	h := sha256.New()
	write := func(parts ...string) {
		for _, part := range parts {
			h.Write([]byte(part))
			h.Write([]byte{0})
		}
	}
	if exe, err := os.Executable(); err == nil {
		if info, err := os.Stat(exe); err == nil {
			write(fmt.Sprintf("%d:%d", info.Size(), info.ModTime().UnixNano()))
		}
	}
	write("verdict-cache-5-truncated-parameter-extension", machine.Arch, "false", nativegen.Describe(machine), source.String(), "")
	write("verify-budget", "")
	oldKey := hex.EncodeToString(h.Sum(nil))
	newKey := verdictCacheKey(machine, source, functions, "", asm.VerificationOptions{})
	if oldKey == newKey {
		t.Fatal("new contract reused old key")
	}
	dir := t.TempDir()
	storeVerdict(dir, oldKey, asm.Verdict{Kind: asm.VerdictProven, Message: "legacy snapshot"})
	if _, hit := cachedVerdict(dir, oldKey, functions); !hit {
		t.Fatal("legacy fixture was not stored")
	}
	if got, hit := cachedVerdict(dir, newKey, functions); hit {
		t.Fatalf("old namespace hit new contract: %+v", got)
	}
}

func TestVerificationOptionsConcurrentCacheIsolation(t *testing.T) {
	dir := t.TempDir()
	var ready, finished sync.WaitGroup
	start := make(chan struct{})
	for i, options := range []asm.VerificationOptions{{}, asm.NewVerificationOptions("components", "high", "")} {
		ready.Add(1)
		finished.Add(1)
		go func(i int, options asm.VerificationOptions) {
			defer finished.Done()
			message := fmt.Sprintf("proof from option snapshot %d", i)
			var candidate *opt.Candidate
			d := func() *nativeDriver {
				defer ready.Done()
				_, source, functions := verificationCacheFixture(t)
				verified, cached := 0, 0
				driver := &nativeDriver{source: source, functions: functions, verificationOptions: options,
					cacheDir: dir, verdicts: map[*asm.Function]asm.Verdict{}, verified: &verified, fromCache: &cached}
				candidate = opt.Identity(nativegen.PlainLane(nativegen.Lane{Arch: asm.ArchArm64}))
				if err := driver.Materialize(candidate); err != nil {
					t.Error(err)
					return nil
				}
				key := verdictCacheKey(candidate.Body.(*asm.Function), source, functions, "", options)
				storeVerdict(dir, key, asm.Verdict{Kind: asm.VerdictProven, Message: message})
				return driver
			}()
			<-start
			if d == nil {
				return
			}
			// Both snapshots have populated the shared directory before either
			// performs its lookup. No syntax, machine, driver or ledger is shared.
			for j := 0; j < 4; j++ {
				got := d.Validate(candidate)
				if !got.Cached || got.Outcome != opt.Proven || got.Message != message {
					t.Errorf("snapshot %d loaded a foreign/missing cache record: %+v", i, got)
					return
				}
			}
		}(i, options)
	}
	ready.Wait()
	close(start)
	finished.Wait()
}
