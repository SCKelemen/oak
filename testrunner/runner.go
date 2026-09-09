package testrunner

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"time"
)

type Config struct {
	Adapter                              string
	EmitFuzz                             string
	CC                                   string
	Profile                              string // discipline profile: "", "default", or "strict"
	Runs, MaxBytes, Shrink, MaxDiscards  int
	Seed                                 uint64
	Timeout, BuildTimeout, ShrinkTimeout time.Duration
	Run, Fuzz, Sim, Replay               string
	JSON, List, Verbose, Sanitize        bool
	Cover                                string
	Workers                              int
	Campaign                             string
}

func Defaults() Config {
	return Config{CC: "cc", Runs: 100, MaxBytes: 256, Shrink: 200, Seed: 1, Timeout: 2 * time.Second, BuildTimeout: time.Minute, ShrinkTimeout: 10 * time.Second, MaxDiscards: 1000, Workers: 1}
}

type Result struct {
	Test
	Commands       []Command    `json:"commands,omitempty"`
	Trace          []TraceEvent `json:"trace,omitempty"`
	TraceText      []string     `json:"trace_text,omitempty"`
	TraceTruncated bool         `json:"trace_truncated,omitempty"`
	// Divergence is set when a strict replay reproduced the failure signature
	// but not the recorded semantic trace.
	Divergence *TraceDivergence `json:"trace_divergence,omitempty"`
	Package    string           `json:"package"`
	Status     string           `json:"status"`
	Cases      int              `json:"cases"`
	Discards   int              `json:"discards"`
	Seed       uint64           `json:"seed"`
	Failure    string           `json:"failure,omitempty"`
	Artifact   string           `json:"artifact,omitempty"`
	Output     string           `json:"output,omitempty"`
	Classes    map[uint32]int   `json:"classes,omitempty"`
	// Attempts is how far the deterministic attempt sequence was consumed,
	// including attempts carried over from a resumed campaign.
	Attempts int `json:"attempts,omitempty"`
	schema   *TraceSchema
}

// setTrace records a trace with its decoded text when the package has a schema.
func (r *Result) setTrace(trace []TraceEvent, truncated bool) {
	r.Trace, r.TraceTruncated = trace, truncated
	r.TraceText = r.schema.describeAll(trace)
}

// Main is usable without os.Exit, including by CLI integration tests.
func Main(args []string, stdout, stderr io.Writer) int {
	cfg := Defaults()
	flags := flag.NewFlagSet("oak test", flag.ContinueOnError)
	flags.SetOutput(stderr)
	flags.StringVar(&cfg.CC, "cc", cfg.CC, "C compiler executable")
	flags.StringVar(&cfg.Profile, "profile", "", "discipline profile: default or strict (docs/spec/85-discipline.md)")
	flags.StringVar(&cfg.Adapter, "adapter", "", "trusted deterministic native adapter manifest (also required for replay)")
	flags.IntVar(&cfg.Runs, "runs", cfg.Runs, "accepted generated cases per property/simulation/fuzz campaign")
	flags.IntVar(&cfg.MaxBytes, "max-bytes", cfg.MaxBytes, "maximum input/choice-tape bytes (0..1048576)")
	flags.Uint64Var(&cfg.Seed, "seed", cfg.Seed, "reproducible root seed")
	flags.IntVar(&cfg.Shrink, "shrink", cfg.Shrink, "maximum minimization executions; 0 disables")
	flags.IntVar(&cfg.MaxDiscards, "max-discards", cfg.MaxDiscards, "maximum rejected generated cases")
	flags.DurationVar(&cfg.Timeout, "timeout", cfg.Timeout, "per-case process timeout")
	flags.DurationVar(&cfg.BuildTimeout, "build-timeout", cfg.BuildTimeout, "per-package C compiler timeout")
	flags.DurationVar(&cfg.ShrinkTimeout, "shrink-timeout", cfg.ShrinkTimeout, "minimization time budget (plus at most one case timeout)")
	flags.StringVar(&cfg.Run, "run", "", "test name regular expression")
	flags.StringVar(&cfg.EmitFuzz, "emit-fuzz-harness", "", "export one -fuzz target as a libFuzzer C harness (new file)")
	flags.StringVar(&cfg.Fuzz, "fuzz", "", "fuzz target regular expression; enables mutation")
	flags.StringVar(&cfg.Sim, "sim", "", "simulation name regular expression")
	flags.StringVar(&cfg.Replay, "replay", "", "replay one saved artifact against its exact build")
	flags.StringVar(&cfg.Cover, "cover", "", "required class sample counts, e.g. 10:5,20:1 (per selected generated test)")
	flags.IntVar(&cfg.Workers, "workers", cfg.Workers, "concurrent case executions (1..64); results are identical for every value")
	flags.StringVar(&cfg.Campaign, "campaign", "", "directory of resumable campaign state per test; rerun with a larger -runs to continue")
	flags.BoolVar(&cfg.JSON, "json", false, "emit one JSON result per test")
	flags.BoolVar(&cfg.List, "list", false, "list matching tests without compilation")
	flags.BoolVar(&cfg.Verbose, "v", false, "include successful test output")
	flags.BoolVar(&cfg.Sanitize, "sanitize", false, "enable native address and undefined-behavior sanitizers")
	flags.Usage = func() {
		fmt.Fprintln(stderr, "Usage: oak test [flags] [directory | ./... ...]\nFlags precede paths. Tests live in *_test.oak files.")
		flags.PrintDefaults()
	}
	if err := flags.Parse(args); err != nil {
		if err == flag.ErrHelp {
			return 0
		}
		return 2
	}
	if cfg.Workers < 1 || cfg.Workers > 64 || cfg.Campaign != "" && cfg.Replay != "" || cfg.Runs < 1 || cfg.Runs > 1000000 || cfg.MaxBytes < 0 || cfg.MaxBytes > 1<<20 || cfg.Shrink < 0 || cfg.MaxDiscards < 0 || cfg.Timeout <= 0 || cfg.BuildTimeout <= 0 || cfg.ShrinkTimeout <= 0 || cfg.Fuzz != "" && cfg.Sim != "" || cfg.Replay != "" && (cfg.Fuzz != "" || cfg.Sim != "" || cfg.Run != "" || cfg.List || cfg.Cover != "") {
		fmt.Fprintln(stderr, "invalid test configuration")
		return 2
	}
	if cfg.Profile != "" && cfg.Profile != "default" && cfg.Profile != "strict" {
		fmt.Fprintf(stderr, "unknown profile %q (default or strict; docs/spec/85-discipline.md section 1)\n", cfg.Profile)
		return 2
	}
	if cfg.EmitFuzz != "" && (cfg.Fuzz == "" || cfg.Replay != "" || cfg.List) {
		fmt.Fprintln(stderr, "-emit-fuzz-harness requires -fuzz and cannot combine with replay/list")
		return 2
	}
	run, err := regexp.Compile(cfg.Run)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	fuzz, err := regexp.Compile(cfg.Fuzz)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	sim, err := regexp.Compile(cfg.Sim)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	cover, err := parseCover(cfg.Cover)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	var replay *Artifact
	if cfg.Replay != "" {
		a, err := readArtifact(cfg.Replay, 1<<20)
		if err != nil {
			fmt.Fprintln(stderr, err)
			return 2
		}
		cfg.Timeout = time.Duration(a.TimeoutNanos)
		cfg.MaxBytes = a.MaxBytes
		cfg.Sanitize = a.Sanitize
		replay = &a
	}
	packages, err := Discover(flags.Args())
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	matched := 0
	for i := range packages {
		packages[i].Profile = cfg.Profile
		var selected []Test
		for _, test := range packages[i].Tests {
			if !run.MatchString(test.Name) || cfg.Fuzz != "" && (test.Kind != "fuzz" || !fuzz.MatchString(test.Name)) || cfg.Sim != "" && (test.Kind != "simulation" || !sim.MatchString(test.Name)) {
				continue
			}
			if replay != nil && (test.Name != replay.Test || test.Kind != replay.Kind) {
				continue
			}
			selected = append(selected, test)
			matched++
		}
		packages[i].Tests = selected
	}
	if matched == 0 {
		fmt.Fprintln(stderr, "no matching Oak tests")
		return 2
	}
	if replay != nil && matched != 1 {
		fmt.Fprintln(stderr, "replay requires exactly one matching test; select its package directory")
		return 2
	}
	if cfg.EmitFuzz != "" {
		if matched != 1 {
			fmt.Fprintln(stderr, "fuzz export requires exactly one matching target")
			return 2
		}
		for _, pkg := range packages {
			if len(pkg.Tests) == 1 {
				adapter, err := loadAdapter(cfg.Adapter)
				content := ""
				if err == nil {
					content, err = emitFuzzHarness(pkg, pkg.Tests[0], cfg.MaxBytes, adapter)
				}
				if err == nil {
					err = writeHarness(cfg.EmitFuzz, content)
				}
				if err != nil {
					fmt.Fprintln(stderr, err)
					return 2
				}
				if cfg.JSON {
					if err := json.NewEncoder(stdout).Encode(map[string]string{"status": "exported", "path": cfg.EmitFuzz}); err != nil {
						return 2
					}
				} else {
					fmt.Fprintln(stdout, "Exported "+cfg.EmitFuzz)
				}
			}
		}
		return 0
	}
	code := 0
	emit := func(result Result) {
		if cfg.JSON {
			if err := json.NewEncoder(stdout).Encode(result); err != nil {
				fmt.Fprintln(stderr, err)
				code = 2
			}
		} else {
			fmt.Fprintf(stdout, "%s %s/%s (%d cases, %d discarded, seed %d)\n", strings.ToUpper(result.Status), result.Package, result.Name, result.Cases, result.Discards, result.Seed)
			if result.Failure != "" {
				fmt.Fprintln(stdout, "  "+result.Failure)
			}
			if result.Artifact != "" {
				adapterFlag := ""
				if cfg.Adapter != "" {
					adapterFlag = fmt.Sprintf(" -adapter %q", cfg.Adapter)
				}
				fmt.Fprintf(stdout, "  replay: oak test%s -replay %q %q\n", adapterFlag, result.Artifact, result.Package)
			}
			if result.Output != "" {
				fmt.Fprintln(stdout, result.Output)
			}
			for i, c := range result.Commands {
				fmt.Fprintf(stdout, "  command[%d] kind=%d target=%d value=%d\n", i, c.Kind, c.Target, c.Value)
			}
			start := len(result.Trace) - 8
			if start < 0 {
				start = 0
			}
			for i := start; i < len(result.Trace); i++ {
				fmt.Fprintf(stdout, "  trace[%d] %s\n", i, result.schema.Describe(result.Trace[i]))
			}
			if d := result.Divergence; d != nil {
				recorded, observed := "trace ended", "trace ended"
				if d.Recorded != nil {
					recorded = result.schema.Describe(*d.Recorded)
				}
				if d.Observed != nil {
					observed = result.schema.Describe(*d.Observed)
				}
				fmt.Fprintf(stdout, "  diverged at trace[%d]: recorded %s; observed %s\n", d.Index, recorded, observed)
			}
			if result.TraceTruncated {
				fmt.Fprintln(stdout, "  trace truncated after 256 events; later events were not recorded")
			}
		}
	}
	for _, pkg := range packages {
		if len(pkg.Tests) == 0 {
			continue
		}
		if cfg.List {
			for _, test := range pkg.Tests {
				emit(Result{Test: test, Package: pkg.Dir, Status: "list", Seed: cfg.Seed})
			}
			continue
		}
		native, err := buildNative(pkg, cfg)
		if err != nil {
			emit(Result{Package: pkg.Dir, Status: "error", Failure: err.Error(), Seed: cfg.Seed})
			code = 2
			continue
		}
		for _, test := range pkg.Tests {
			index := 0
			for i, registered := range pkg.Registry {
				if registered.Name == test.Name {
					index = i
					break
				}
			}
			result := runTest(pkg, test, index, native, cfg, cover, replay)
			if result.Status == "error" {
				code = 2
			}
			if result.Status != "pass" && code == 0 {
				code = 1
			}
			emit(result)
		}
		_ = os.RemoveAll(native.dir)
	}
	return code
}

func parseCover(raw string) (map[uint32]int, error) {
	result := map[uint32]int{}
	if raw == "" {
		return result, nil
	}
	for _, item := range strings.Split(raw, ",") {
		parts := strings.Split(item, ":")
		if len(parts) != 2 {
			return nil, fmt.Errorf("invalid coverage requirement %q", item)
		}
		id, err := strconv.ParseUint(parts[0], 10, 32)
		if err != nil {
			return nil, err
		}
		count, err := strconv.Atoi(parts[1])
		if err != nil || count < 1 {
			return nil, fmt.Errorf("coverage count must be positive")
		}
		result[uint32(id)] = count
	}
	return result, nil
}

func runTest(pkg Package, test Test, index int, native *nativeProgram, cfg Config, cover map[uint32]int, replay *Artifact) Result {
	result := Result{Test: test, Package: pkg.Dir, Status: "pass", Seed: cfg.Seed, Classes: map[uint32]int{}, schema: pkg.Schema}
	format := ""
	generator := -1
	if test.Generator != "" {
		format = commandFormat
		for i, t := range pkg.Registry {
			if t.Name == test.Generator {
				generator = i
				break
			}
		}
		if generator < 0 {
			result.Status, result.Failure = "error", "missing command generator"
			return result
		}
	}
	if replay != nil {
		if replay.InputFormat != format {
			result.Status, result.Failure = "error", "replay input format mismatch"
			return result
		}
		result.Seed = replay.Seed
		if replay.Build != native.build {
			result.Status = "error"
			result.Failure = "replay build mismatch: use the original source, toolchain and configuration; ordinary oak test reruns corpus inputs across builds"
			return result
		}
		out := native.run(index, replay.Input)
		result.Cases = 1
		result.Output = out.output
		result.setTrace(out.trace, out.traceTruncated)
		if format != "" {
			result.Commands = decodeCommands(replay.Input)
		}
		if out.status == "fail" && out.signature == replay.Signature {
			result.Status = "fail"
			result.Failure = "reproduced " + out.signature
			if replay.TraceVersion == traceVersion && !sameTrace(out, outcome{trace: replay.Trace, traceTruncated: replay.TraceTruncated}) {
				result.Status = "error"
				result.Divergence = divergence(replay.Trace, out.trace)
				if result.Divergence != nil {
					result.Failure = fmt.Sprintf("replay trace diverged at event %d despite matching failure signature", result.Divergence.Index)
				} else {
					result.Failure = "replay trace truncation flag diverged despite matching failure signature"
				}
			}
		} else {
			result.Status = "error"
			result.Failure = fmt.Sprintf("replay diverged: expected %s, got %s %s", replay.Signature, out.status, out.signature)
		}
		return result
	}
	corpus, err := loadCorpus(pkg, test, cfg.MaxBytes)
	if err != nil {
		result.Status = "error"
		result.Failure = err.Error()
		return result
	}
	// consume records one executed case in attempt order; execute runs and
	// consumes sequentially (unit tests, corpus). Generated attempts are
	// prepared by workers and consumed in order, so the reported outcome,
	// counts and minimized failure are the same for every worker count.
	consume := func(input []byte, out outcome, attempt int) bool {
		if out.status == "discard" {
			result.Discards++
			if test.Kind == "unit" || result.Discards > cfg.MaxDiscards {
				result.Status = "fail"
				result.Failure = "discard budget exhausted; rejected inputs are not passing tests"
				return false
			}
			return true
		}
		result.Cases++
		if out.status == "pass" {
			for id := range out.classes {
				result.Classes[id]++
			}
			if cfg.Verbose && len(result.Output) < outputLimit {
				result.Output += out.output
			}
			return true
		}
		result.Status = "fail"
		result.Failure = out.signature
		result.Output = out.output
		best := input
		// Timeouts and infrastructure failures are not stable shrink predicates.
		if test.Kind != "unit" && cfg.Shrink > 0 && out.signature != "timeout" && !strings.HasPrefix(out.signature, "harness:") {
			confirmation := native.run(index, input)
			if confirmation.status != "fail" || confirmation.signature != out.signature || !sameTrace(confirmation, out) {
				result.Failure = "non-reproducible failure: " + out.signature
			} else {
				ctx, cancel := context.WithTimeout(context.Background(), cfg.ShrinkTimeout)
				bestOutcome := confirmation
				minimize := Minimize
				if format != "" {
					minimize = MinimizeCommands
				}
				best = minimize(ctx, input, cfg.Shrink, func(candidate []byte) bool {
					r := native.run(index, candidate)
					matches := r.status == "fail" && r.signature == out.signature
					if matches {
						bestOutcome = r
					}
					return matches
				})
				cancel()
				final := native.run(index, best)
				if final.status == "fail" && final.signature == out.signature && sameTrace(final, bestOutcome) {
					out = final
				} else {
					best = input
					result.Failure = "non-reproducible minimized failure: " + out.signature
				}
			}
		}
		result.setTrace(out.trace, out.traceTruncated)
		result.Output = out.output
		if format != "" {
			result.Commands = decodeCommands(best)
		}
		artifact := Artifact{TimeoutNanos: int64(cfg.Timeout), Version: 1, Engine: engineVersion, Test: test.Name, Kind: test.Kind, Build: native.build, Seed: cfg.Seed, Attempt: attempt, MaxBytes: cfg.MaxBytes, Sanitize: cfg.Sanitize, Signature: out.signature, Input: best}
		artifact.InputFormat = format
		artifact.TraceVersion, artifact.Trace, artifact.TraceTruncated = traceVersion, out.trace, out.traceTruncated
		path, err := saveArtifact(pkg, test, artifact)
		if err != nil {
			result.Failure += "; cannot save failure: " + err.Error()
		} else {
			result.Artifact = path
		}
		return false
	}
	execute := func(input []byte, attempt int) bool {
		if format != "" && (len(input)%commandWidth != 0 || len(input)/commandWidth > commandLimit) {
			result.Status, result.Failure = "error", "invalid concrete command corpus: expected at most 256 complete 12-byte commands"
			return false
		}
		return consume(input, native.run(index, input), attempt)
	}
	if test.Kind == "unit" {
		execute(nil, 0)
		return result
	}
	// Regression corpus is always run before new inputs. Build identities are
	// intentionally not enforced here: regressions should survive source edits.
	for i, input := range corpus {
		if !execute(input, -1-i) {
			return result
		}
	}
	seeds := append([][]byte{}, corpus...)
	for i := 0; i < 4; i++ {
		r := randomFor(cfg.Seed, test.Name, i)
		seeds = append(seeds, generate(&r, i, cfg.MaxBytes))
	}
	if test.Kind == "fuzz" && cfg.Fuzz == "" {
		for i, input := range seeds[len(corpus):] {
			if !execute(input, i) {
				return result
			}
		}
	} else {
		type prepared struct {
			input     []byte
			out       outcome
			generated *outcome
		}
		prepare := func(attempt int) prepared {
			r := randomFor(cfg.Seed, test.Name, attempt)
			input := generate(&r, attempt, cfg.MaxBytes)
			if generator >= 0 {
				generated := native.run(generator, input)
				if generated.status != "pass" {
					return prepared{generated: &generated}
				}
				input = encodeCommands(generated.commands)
			}
			if test.Kind == "fuzz" && attempt >= len(seeds) {
				input = mutate(&r, seeds, cfg.MaxBytes)
			} else if test.Kind == "fuzz" {
				input = seeds[attempt]
			}
			return prepared{input: input, out: native.run(index, input)}
		}
		accepted := 0
		attempt := 0
		state := campaignState{Version: 1, Engine: engineVersion, Build: native.build, Test: test.Name, Kind: test.Kind, Seed: cfg.Seed, MaxBytes: cfg.MaxBytes, Sanitize: cfg.Sanitize}
		statePath := ""
		if cfg.Campaign != "" {
			statePath = campaignPath(cfg.Campaign, pkg, test)
			saved, err := loadCampaign(statePath, state)
			if err != nil {
				result.Status, result.Failure = "error", err.Error()
				return result
			}
			if saved != nil {
				attempt, accepted = saved.NextAttempt, saved.Accepted
				result.Cases, result.Discards = saved.Cases, saved.Discards
				for key, count := range saved.Classes {
					id, _ := strconv.ParseUint(key, 10, 32)
					result.Classes[uint32(id)] += count
				}
			}
		}
		checkpoint := func() {
			result.Attempts = attempt
			if statePath == "" {
				return
			}
			state.NextAttempt, state.Accepted, state.Cases, state.Discards = attempt, accepted, result.Cases, result.Discards
			state.Classes = map[string]int{}
			for id, count := range result.Classes {
				state.Classes[strconv.FormatUint(uint64(id), 10)] = count
			}
			if err := saveCampaign(statePath, state); err != nil {
				result.Status, result.Failure = "error", "cannot save campaign state: "+err.Error()
			}
		}
		for accepted < cfg.Runs && result.Status != "error" {
			batch := make([]prepared, cfg.Workers)
			var wg sync.WaitGroup
			for i := range batch {
				wg.Add(1)
				go func(i int) {
					defer wg.Done()
					batch[i] = prepare(attempt + i)
				}(i)
			}
			wg.Wait()
			stop := false
			for i := range batch {
				if accepted >= cfg.Runs {
					break
				}
				item := batch[i]
				attempt++
				if item.generated != nil {
					if item.generated.status == "discard" {
						result.Discards++
						if result.Discards > cfg.MaxDiscards {
							result.Status, result.Failure = "fail", "generator discard budget exhausted"
							stop = true
							break
						}
						continue
					}
					result.Status, result.Failure, result.Output = "error", "command generator failed: "+item.generated.signature, item.generated.output
					result.setTrace(item.generated.trace, item.generated.traceTruncated)
					stop = true
					break
				}
				before := result.Cases
				if !consume(item.input, item.out, attempt-1) {
					stop = true
					break
				}
				if result.Cases > before {
					accepted++
				}
			}
			checkpoint()
			if stop {
				return result
			}
		}
		result.Attempts = attempt
	}
	if result.Cases == 0 {
		result.Status = "fail"
		result.Failure = "no accepted cases"
	}
	for id, min := range cover {
		if result.Classes[id] < min {
			result.Status = "fail"
			result.Failure += fmt.Sprintf(" class %d covered by %d cases, require %d;", id, result.Classes[id], min)
		}
	}
	return result
}
