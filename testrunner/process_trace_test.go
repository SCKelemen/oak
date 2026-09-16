package testrunner

import (
	"bytes"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"testing"
)

// Compare with what a real child observes, using an explicit synthetic
// environment so this test never needs to report the host's environment.
func TestProcessTraceObservedContext(t *testing.T) {
	if os.Getenv("OAK_PROCESS_TRACE_CHILD") == "1" {
		cwd, err := os.Getwd()
		if err != nil {
			os.Exit(2)
		}
		_ = json.NewEncoder(os.Stdout).Encode(processContext{Argv: os.Args, CWD: cwd, Env: os.Environ()})
		os.Exit(0)
	}
	binary, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	dir := filepath.Join(t.TempDir(), "child working directory")
	if err := os.Mkdir(dir, 0700); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(binary, "-test.run=^TestProcessTraceObservedContext$", "argument with spaces")
	cmd.Dir = dir
	cmd.Env = []string{"OAK_PROCESS_TRACE_CHILD=1", "SAMPLE=stale", "SAMPLE=quoted \"value\"\nand newline", "PWD=" + dir}
	var trace, output bytes.Buffer
	tracer := &processTracer{out: &trace}
	tracer.command("probe", dir, cmd)
	cmd.Stdout, cmd.Stderr = &output, &output
	if err := cmd.Run(); err != nil {
		t.Fatalf("child probe: %v", err)
	}
	var recorded, observed processContext
	if err := json.Unmarshal(trace.Bytes(), &recorded); err != nil {
		t.Fatal(err)
	}
	if err := json.Unmarshal(output.Bytes(), &observed); err != nil {
		t.Fatal(err)
	}
	if recorded.Executable != binary || !reflect.DeepEqual(recorded.Argv, observed.Argv) || recorded.CWD != observed.CWD || !reflect.DeepEqual(recorded.Env, observed.Env) {
		t.Fatalf("launch context differs from observed child context: recorded %+v, observed %+v", recorded, observed)
	}
}

// F31: process diagnostics are separate from result JSON and test output,
// and distinguish a resident fork from a fresh executable invocation.
func TestProcessTracing(t *testing.T) {
	const sample = "spaces, \"quotes\", and a newline\nsecond=value"
	t.Setenv("OAK_PROCESS_TRACE_SAMPLE", sample)
	dir := fixture(t, map[string]string{"a_test.oak": `import(testing)
TestPass: (): () { test_check(true, u32(1)) }
TestFail: (): () { test_check(false, u32(2)) }
PropertyConcurrent: (data: []u8): () { test_check(len(data) <= u32(256), u32(3)) }
`})
	cwd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	for _, mode := range []string{"off", "exec", "fork"} {
		t.Run(mode, func(t *testing.T) {
			if mode == "fork" && !residentSupported {
				t.Skip("resident workers require fork")
			}
			args := []string{"-workers", "4", "-runs", "8", "-shrink", "0"}
			if mode != "off" {
				args = append(args, "-trace-processes", "-resident="+strconv.FormatBool(mode == "fork"))
			}
			code, results, stderr := runCLI(t, append(args, dir)...)
			// Do not dump stderr here: a process trace includes the host's
			// full environment. Assertions report only the field at fault.
			if code != 1 || len(results) != 3 {
				t.Fatalf("code %d, %d results; want one failed test among three", code, len(results))
			}
			for _, result := range results {
				if result.Output != "" {
					t.Fatalf("process trace entered test output for %s", result.Name)
				}
				if result.Name == "TestFail" && result.Failure != "invariant:2" {
					t.Fatalf("failure changed: %q", result.Failure)
				}
			}
			if mode == "off" {
				if stderr != "" {
					t.Fatal("process diagnostics must be opt-in")
				}
				return
			}
			seen := map[string]int{}
			for _, line := range strings.Split(strings.TrimSpace(stderr), "\n") {
				var record struct {
					Event, Phase, Mode, Package, Test, CWD, Report, Executable string
					Argv, Env                                                  []string
					Index                                                      *int
					WorkerPID                                                  int `json:"worker_pid"`
				}
				if err := json.Unmarshal([]byte(line), &record); err != nil {
					t.Fatal("process trace contains a malformed JSON line")
				}
				if record.Event != "oak-test-process" || record.Package != dir || record.Executable == "" {
					t.Fatal("process trace lacks its event, package or executable")
				}
				found := false
				for _, entry := range record.Env {
					found = found || entry == "OAK_PROCESS_TRACE_SAMPLE="+sample
				}
				if !found {
					t.Fatal("launch environment lost the sample value or its escaping")
				}
				if record.Phase != "case" {
					continue
				}
				seen[record.Test]++
				if record.Mode != mode || record.CWD != cwd || record.Index == nil || record.Report == "" {
					t.Fatalf("case %s lacks its mode, cwd, index or report path", record.Test)
				}
				if mode == "fork" {
					if len(record.Argv) != 2 || record.Argv[1] != "serve" || record.WorkerPID <= 0 {
						t.Fatal("fork request must identify the actual resident argv and worker")
					}
				} else if len(record.Argv) != 3 || record.Argv[1] != strconv.Itoa(*record.Index) || record.Argv[2] != record.Report {
					t.Fatal("exec trace must identify the actual case argv")
				}
			}
			for name, count := range map[string]int{"TestPass": 1, "TestFail": 1, "PropertyConcurrent": 8} {
				if seen[name] != count {
					t.Errorf("%s: %d traced cases, want %d", name, seen[name], count)
				}
			}
		})
	}
}
