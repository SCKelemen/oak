package main

// The profile mode is a test-harness diagnostic. It cannot produce a native
// prerequisite, run a solver, change a verification budget, or select a name
// supplied by its caller. The outer hosted owner supplies the hard deadline.
import (
	"bytes"
	"crypto/sha256"
	"debug/elf"
	_ "embed"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"os/signal"
	"path/filepath"
	"reflect"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/internal/nativetiming"
	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/target"
)

//go:embed .github/scripts/native_scalar_text_profile_inputs.json
var scalarProfileInputsJSON []byte

const scalarProfileLimit = 8 << 20
const scalarProfileJSONLimit = 1 << 20

type scalarProfileInputs struct {
	Sources        map[string]string   `json:"sources"`
	SupportSources map[string]string   `json:"support_sources"`
	GoBuild        nativeProverGoBuild `json:"go_build"`
	CandidateNames []string            `json:"candidate_names"`
}

type scalarProfileFile struct {
	Bytes  int64  `json:"bytes"`
	SHA256 string `json:"sha256"`
}

type scalarProfileResult struct {
	SchemaVersion      int                          `json:"schema_version"`
	Kind               string                       `json:"kind"`
	Status             string                       `json:"status"`
	Error              string                       `json:"error"`
	Selector           string                       `json:"selector"`
	Comparable         bool                         `json:"comparable"`
	EmitCompleted      bool                         `json:"emit_completed"`
	ReportCount        int                          `json:"report_count"`
	CandidateNames     []string                     `json:"candidate_names"`
	Profiles           map[string]scalarProfileFile `json:"profiles"`
	InputsSHA256       string                       `json:"inputs_sha256"`
	OuterContextSHA256 string                       `json:"outer_context_sha256"`
	HarnessSHA256      string                       `json:"harness_sha256"`
	BlockRate          int                          `json:"block_rate_ns"`
	MutexFraction      int                          `json:"mutex_fraction"`
	ElapsedNS          int64                        `json:"elapsed_ns"`
	ProfileStartedNS   int64                        `json:"profile_started_unix_ns"`
	ProfileStoppedNS   int64                        `json:"profile_stopped_unix_ns"`
}

// Write errors and capacity exhaustion are sticky. CPU profiling owns its
// writer goroutine: only notify the coordinator here, never StopCPUProfile.
// The bounded prefix remains on disk and is explicitly incomplete on failure.
type scalarProfileWriter struct {
	mu        sync.Mutex
	w         io.Writer
	remaining int64
	failed    error
	notify    chan struct{}
}

func (w *scalarProfileWriter) Write(p []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()
	fail := func(err error) {
		if w.failed == nil {
			w.failed = err
			select {
			case w.notify <- struct{}{}:
			default:
			}
		}
	}
	if w.failed != nil {
		return 0, w.failed
	}
	if int64(len(p)) > w.remaining {
		fail(errors.New("profile capacity exceeded"))
		return 0, w.failed
	}
	n, err := w.w.Write(p)
	if n < 0 || n > len(p) {
		fail(errors.New("invalid profile write count"))
		return 0, w.failed
	}
	w.remaining -= int64(n)
	if err != nil {
		fail(err)
	} else if n != len(p) {
		fail(io.ErrShortWrite)
	}
	return n, w.failed
}

func (w *scalarProfileWriter) failure() error { w.mu.Lock(); defer w.mu.Unlock(); return w.failed }

// Owned private directories and the outer immutable-checkout contract are
// prerequisites. Bind the named regular file to the descriptor before/after
// each bounded read, without treating access-time updates as mutation.
func scalarProfileRead(path string, limit int64) ([]byte, error) {
	before, err := os.Lstat(path)
	if err != nil {
		return nil, err
	}
	if !before.Mode().IsRegular() || before.Size() > limit {
		return nil, errors.New("profile input is not bounded regular data")
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	opened, err := f.Stat()
	if err != nil || !os.SameFile(before, opened) {
		return nil, errors.New("profile input identity changed")
	}
	b, err := io.ReadAll(io.LimitReader(f, limit+1))
	if err != nil {
		return nil, err
	}
	after, err := f.Stat()
	if err != nil {
		return nil, err
	}
	named, err := os.Lstat(path)
	if err != nil || !named.Mode().IsRegular() || !os.SameFile(opened, named) || !os.SameFile(opened, after) || opened.Size() != after.Size() || opened.ModTime() != after.ModTime() || opened.Mode() != after.Mode() || int64(len(b)) != opened.Size() || int64(len(b)) > limit {
		return nil, errors.New("profile input changed while reading")
	}
	return b, nil
}

func scalarProfileWriteJSON(path string, value any, remaining *int64) error {
	b, err := json.Marshal(value)
	if err != nil {
		return err
	}
	b = append(b, '\n')
	if int64(len(b)) > *remaining {
		return errors.New("profile JSON capacity exceeded")
	}
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
	if err != nil {
		return err
	}
	n, writeErr := f.Write(b)
	syncErr := f.Sync()
	closeErr := f.Close()
	*remaining -= int64(n)
	if writeErr != nil {
		return writeErr
	}
	if n != len(b) {
		return io.ErrShortWrite
	}
	if syncErr != nil {
		return syncErr
	}
	return closeErr
}

func scalarProfileCheckSources(directory string, locked scalarProfileInputs) error {
	expected := oakSolverSources()
	if len(expected) != 19 || len(locked.Sources) != 19 {
		return errors.New("profile requires exactly nineteen sources")
	}
	dir, err := os.Open(directory)
	if err != nil {
		return err
	}
	names, readErr := dir.Readdirnames(20)
	closeErr := dir.Close()
	if readErr != nil && readErr != io.EOF {
		return readErr
	}
	if closeErr != nil {
		return closeErr
	}
	if len(names) != 19 {
		return errors.New("unexpected profile source member")
	}
	for _, name := range names {
		text, ok := expected[name]
		if !ok {
			return errors.New("unexpected profile source name")
		}
		b, err := scalarProfileRead(filepath.Join(directory, name), 1<<20)
		if err != nil {
			return err
		}
		if string(b) != text || nativeDigest(b) != locked.Sources[name] {
			return fmt.Errorf("profile source mismatch: %s", name)
		}
	}
	support := map[string]string{"stdlib/std.oak": stdlib.Prelude, "stdlib/host.oak": stdlib.Packages["host"]}
	if len(locked.SupportSources) != len(support) {
		return errors.New("profile support inventory mismatch")
	}
	for name, value := range support {
		b, err := scalarProfileRead(name, 1<<20)
		if err != nil {
			return err
		}
		if nativeDigest([]byte(value)) != locked.SupportSources[name] || nativeDigest(b) != locked.SupportSources[name] {
			return fmt.Errorf("profile support mismatch: %s", name)
		}
	}
	return nil
}

func scalarProfileCheckBuild(info *debug.BuildInfo, expected nativeProverGoBuild) error {
	if info == nil || info.GoVersion != "go1.27.1" || info.GoVersion != expected.Version || !reflect.DeepEqual(info.Main, expected.Main) || !reflect.DeepEqual(info.Deps, expected.Dependencies) {
		return errors.New("profile Go identity mismatch")
	}
	settings := map[string]string{}
	for _, s := range info.Settings {
		if _, exists := settings[s.Key]; exists {
			return errors.New("duplicate Go setting")
		}
		settings[s.Key] = s.Value
	}
	for name, value := range expected.Settings {
		if settings[name] != value {
			return fmt.Errorf("profile Go setting mismatch: %s", name)
		}
	}
	if settings["-race"] != "true" || settings["CGO_ENABLED"] != "1" || settings["GOOS"] != "linux" || settings["GOARCH"] != "arm64" || settings["GOARM64"] != "v8.0" {
		return errors.New("profile requires native ARM64 race harness")
	}
	return nil
}

// Inventory equality binds the frontend produced by this one real EmitNative
// call. It does not invoke NativeInventory or claim a second frontend run.
func scalarProfileCheckReport(report compiler.NativeBuildReport, locked scalarProfileInputs) error {
	var expected compiler.NativeBuildInventory
	if err := nativeDecode(nativeProverInventoryJSON, &expected); err != nil {
		return err
	}
	if err := nativeValidateInventory(expected); err != nil {
		return err
	}
	if report.SchemaVersion != 2 || !reflect.DeepEqual(report.Inventory, expected) || len(report.Functions) != len(expected.Eligible) || len(report.Supplied) != len(expected.Supplied) {
		return errors.New("profile frontend report inventory mismatch")
	}
	selected := 0
	for i, row := range report.Functions {
		if row.Input != expected.Eligible[i] {
			return errors.New("profile report order/input mismatch")
		}
		if row.Input.Name != "scalar_text" {
			if len(row.Validations) != 0 || row.Selected != nil || row.Status != "c-fallback" {
				return errors.New("profile selector escaped scalar_text")
			}
			continue
		}
		selected++
		if len(locked.CandidateNames) != 3 || len(row.Validations) != 3 || row.Considered < row.Materialized || row.Materialized < 3 || row.Reason == "" {
			return errors.New("profile requires three ordinary completed validations")
		}
		for n, c := range row.Validations {
			if c.Name != locked.CandidateNames[n] || c.Cached || !scalarProfileDigest(c.BodySHA256) || !scalarProfileDigest(c.RecipeSHA256) {
				return errors.New("profile candidate identity/order/cache mismatch")
			}
			switch c.Outcome {
			case "proven", "witnessed", "trusted", "mismatch", "refused":
			default:
				return errors.New("profile candidate verdict missing")
			}
		}
		if row.Selected == nil {
			return errors.New("profile has no actual final selection")
		}
		found := false
		for _, c := range row.Validations {
			if c == *row.Selected {
				found = true
			}
		}
		if !found {
			return errors.New("profile selected candidate not validated")
		}
		switch row.Selected.Outcome {
		case "proven", "witnessed", "trusted":
		default:
			return errors.New("profile final selection refused")
		}
		if row.Status != "c-fallback" && row.Status != row.Selected.Outcome {
			return errors.New("profile terminal verdict mismatch")
		}
	}
	if selected != 1 {
		return errors.New("profile requires one scalar_text row")
	}
	for i, row := range report.Supplied {
		input := expected.Supplied[i]
		if row.Input != input.Input || row.Arch != input.Arch || row.BodySHA256 != input.BodySHA256 || row.Reason == "" {
			return errors.New("profile supplied input mismatch")
		}
		switch row.Status {
		case "proven", "witnessed", "trusted":
		default:
			return errors.New("profile supplied obligation incomplete")
		}
	}
	return nil
}

func scalarProfileDigest(s string) bool {
	b, err := hex.DecodeString(s)
	return err == nil && len(b) == sha256.Size && strings.ToLower(s) == s
}

func scalarProfileSelector(run func() error) error {
	if err := nativeCheckEnvironmentControls(); err != nil {
		return err
	}
	old, existed := os.LookupEnv("OAK_NATIVE_ONLY")
	if err := os.Setenv("OAK_NATIVE_ONLY", "scalar_text"); err != nil {
		return err
	}
	defer func() {
		if existed {
			_ = os.Setenv("OAK_NATIVE_ONLY", old)
		} else {
			_ = os.Unsetenv("OAK_NATIVE_ONLY")
		}
	}()
	return run()
}

func scalarTextProfileMain(args []string) int {
	if len(args) != 1 {
		fmt.Fprintln(os.Stderr, "native-scalar-text-profile requires exactly one new output directory")
		return 2
	}
	if err := scalarTextProfile(args[0]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 1
	}
	return 0
}

func scalarTextProfile(directory string) (failure error) {
	started := time.Now()
	if err := nativeCheckEnvironment(); err != nil {
		return err
	}
	deadlineNS, err := strconv.ParseInt(os.Getenv("SCALAR_PROFILE_DEADLINE_UNIX_NS"), 10, 64)
	if err != nil {
		return errors.New("missing outer profile deadline")
	}
	allowance := time.Until(time.Unix(0, deadlineNS))
	if allowance <= 30*time.Second || allowance > 660*time.Second {
		return errors.New("invalid outer profile allowance")
	}
	// Convert once to this process's monotonic clock. The outer original
	// monotonic deadline remains authoritative despite wall-clock adjustment.
	deadline := started.Add(allowance)
	if err := os.Mkdir(directory, 0o700); err != nil {
		return err
	}
	remainingJSON := int64(scalarProfileJSONLimit)
	result := scalarProfileResult{SchemaVersion: 1, Kind: "scalar-text-profile-diagnostic", Status: "incomplete", Selector: "scalar_text", Profiles: map[string]scalarProfileFile{}, CandidateNames: []string{}, InputsSHA256: nativeDigest(scalarProfileInputsJSON), BlockRate: 1000000, MutexFraction: 100}
	defer func() {
		result.ElapsedNS = time.Since(started).Nanoseconds()
		if failure != nil {
			result.Status = "incomplete"
			result.Comparable = false
			result.Error = failure.Error()
			if len(result.Error) > 4096 {
				result.Error = result.Error[:4096]
			}
		}
		if err := scalarProfileWriteJSON(filepath.Join(directory, "result.json"), result, &remainingJSON); err != nil {
			failure = errors.Join(failure, err)
		}
	}()
	var locked scalarProfileInputs
	if err := nativeDecode(scalarProfileInputsJSON, &locked); err != nil {
		return err
	}
	info, ok := debug.ReadBuildInfo()
	if !ok {
		return errors.New("missing profile build metadata")
	}
	if err := scalarProfileCheckBuild(info, locked.GoBuild); err != nil {
		return err
	}
	outerBytes, err := scalarProfileRead(os.Getenv("SCALAR_PROFILE_CONTEXT"), 128<<10)
	if err != nil {
		return err
	}
	var outer struct {
		HarnessSHA256 string `json:"harness_sha256"`
	}
	if err := json.Unmarshal(outerBytes, &outer); err != nil || !scalarProfileDigest(outer.HarnessSHA256) {
		return errors.New("invalid profile outer harness binding")
	}
	result.OuterContextSHA256 = nativeDigest(outerBytes)
	executable, err := os.Executable()
	if err != nil {
		return err
	}
	binary, err := scalarProfileRead(executable, 128<<20)
	if err != nil {
		return err
	}
	result.HarnessSHA256 = nativeDigest(binary)
	if result.HarnessSHA256 != outer.HarnessSHA256 {
		return errors.New("profile harness bytes differ from owner")
	}
	elfFile, err := elf.NewFile(bytes.NewReader(binary))
	if err != nil {
		return err
	}
	if elfFile.Machine != elf.EM_AARCH64 || elfFile.Class != elf.ELFCLASS64 || elfFile.Data != elf.ELFDATA2LSB || (elfFile.Type != elf.ET_EXEC && elfFile.Type != elf.ET_DYN) {
		elfFile.Close()
		return errors.New("profile harness ELF identity mismatch")
	}
	elfFile.Close()
	binary = nil
	sourceDir := filepath.Join(directory, "source")
	if err := nativeWriteSources(sourceDir); err != nil {
		return err
	}
	if err := scalarProfileCheckSources(sourceDir, locked); err != nil {
		return err
	}
	context := struct {
		Inputs             scalarProfileInputs `json:"inputs"`
		GoBuild            *debug.BuildInfo    `json:"go_build"`
		OuterContextSHA256 string              `json:"outer_context_sha256"`
		HarnessSHA256      string              `json:"harness_sha256"`
		NumCPU             int                 `json:"num_cpu"`
		GOMAXPROCS         int                 `json:"gomaxprocs"`
		GOGC               string              `json:"gogc_environment"`
		Target             string              `json:"target"`
		COptLevel          int                 `json:"c_opt_level"`
	}{locked, info, result.OuterContextSHA256, result.HarnessSHA256, runtime.NumCPU(), runtime.GOMAXPROCS(0), os.Getenv("GOGC"), target.Host().String(), cOptLevel}
	contextCap := int64(128 << 10)
	if err := scalarProfileWriteJSON(filepath.Join(directory, "context.json"), context, &contextCap); err != nil {
		return err
	}
	remainingJSON -= (128 << 10) - contextCap
	if time.Since(started) >= 30*time.Second || time.Until(deadline) <= 30*time.Second {
		return errors.New("profile setup deadline exceeded")
	}
	notify := make(chan struct{}, 1)
	files := map[string]*os.File{}
	writers := map[string]*scalarProfileWriter{}
	defer func() {
		for _, f := range files {
			if err := f.Close(); err != nil {
				failure = errors.Join(failure, err)
			}
		}
	}()
	for _, name := range []string{"cpu", "block", "mutex"} {
		f, err := os.OpenFile(filepath.Join(directory, name+".pprof"), os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0o600)
		if err != nil {
			return err
		}
		files[name] = f
		writers[name] = &scalarProfileWriter{w: f, remaining: scalarProfileLimit, notify: notify}
	}
	signals := make(chan os.Signal, 1)
	signal.Notify(signals, os.Interrupt, syscall.SIGTERM)
	defer signal.Stop(signals)
	timing, err := nativetiming.Start(os.Stderr)
	if err != nil {
		return err
	}
	defer func() { failure = errors.Join(failure, timing.Close()) }()
	return scalarProfileSelector(func() error {
		runtime.SetBlockProfileRate(result.BlockRate)
		previousMutex := runtime.SetMutexProfileFraction(result.MutexFraction)
		defer runtime.SetBlockProfileRate(0)
		defer runtime.SetMutexProfileFraction(previousMutex)
		if previousMutex != 0 {
			return errors.New("profile requires fresh mutex sampling state")
		}
		if err := pprof.StartCPUProfile(writers["cpu"]); err != nil {
			return err
		}
		result.ProfileStartedNS = time.Now().UnixNano()
		type completed struct {
			report compiler.NativeBuildReport
			count  int
			err    error
		}
		done := make(chan completed, 1)
		searchStop := time.Now().Add(600 * time.Second)
		if latest := deadline.Add(-30 * time.Second); latest.Before(searchStop) {
			searchStop = latest
		}
		go func() {
			var value completed
			comp := compiler.New().WithPackageDir(sourceDir).WithNativeBodies().WithVerifyFresh().WithNativeBuildReport(func(report compiler.NativeBuildReport) { value.report, value.count = report, value.count+1 })
			_, _, value.err = emitFor(comp, "native", target.Host(), "")
			done <- value
		}()
		timer := time.NewTimer(time.Until(searchStop))
		defer timer.Stop()
		var value completed
		var runErr error
		select {
		case value = <-done:
			result.EmitCompleted, result.ReportCount = true, value.count
			runErr = value.err
		case <-notify:
			runErr = errors.New("profile writer failed or overflowed")
		case <-timer.C:
			runErr = errors.New("profile search deadline exceeded")
		case <-signals:
			runErr = errors.New("profile interrupted by owner")
		}
		// Only this coordinator stops and joins pprof's CPU writer. Compiler
		// goroutines on an interrupted path end at TestMain os.Exit, not here.
		pprof.StopCPUProfile()
		runtime.SetBlockProfileRate(0)
		runtime.SetMutexProfileFraction(0)
		result.ProfileStoppedNS = time.Now().UnixNano()
		for _, name := range []string{"block", "mutex"} {
			if err := pprof.Lookup(name).WriteTo(writers[name], 0); err != nil {
				runErr = errors.Join(runErr, err)
			}
		}
		for _, name := range []string{"cpu", "block", "mutex"} {
			if err := writers[name].failure(); err != nil {
				runErr = errors.Join(runErr, err)
			}
			if err := files[name].Sync(); err != nil {
				runErr = errors.Join(runErr, err)
			}
			if err := files[name].Close(); err != nil {
				runErr = errors.Join(runErr, err)
			}
			delete(files, name)
			b, err := scalarProfileRead(filepath.Join(directory, name+".pprof"), scalarProfileLimit)
			if err != nil {
				runErr = errors.Join(runErr, err)
			} else {
				if len(b) == 0 {
					runErr = errors.Join(runErr, errors.New("empty profile"))
				}
				result.Profiles[name+".pprof"] = scalarProfileFile{int64(len(b)), nativeDigest(b)}
			}
		}
		if !result.EmitCompleted {
			return runErr
		}
		if value.count != 1 {
			runErr = errors.Join(runErr, errors.New("profile requires one native report"))
		}
		if err := scalarProfileCheckSources(sourceDir, locked); err != nil {
			runErr = errors.Join(runErr, err)
		}
		if value.count == 1 {
			reportCap := int64(768 << 10)
			if err := scalarProfileWriteJSON(filepath.Join(directory, "report.json"), value.report, &reportCap); err != nil {
				runErr = errors.Join(runErr, err)
			}
			remainingJSON -= (768 << 10) - reportCap
			if err := scalarProfileCheckReport(value.report, locked); err != nil {
				runErr = errors.Join(runErr, err)
			} else {
				result.CandidateNames = append([]string{}, locked.CandidateNames...)
				result.Comparable = true
			}
		}
		if !time.Now().Before(deadline) {
			runErr = errors.Join(runErr, errors.New("profile finalization deadline exceeded"))
		}
		if runErr == nil {
			result.Status = "diagnostic_complete_pending_outer_validation"
		}
		return runErr
	})
}
