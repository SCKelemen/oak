package testrunner

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"github.com/SCKelemen/oak/buildcache"
	"github.com/SCKelemen/oak/codegen/metal"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/toolchain"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"time"
)

const engineVersion = "oak-test-v1-splitmix64-choice-bytes"
const outputLimit = 64 * 1024

type limitedBuffer struct {
	bytes.Buffer
	truncated bool
}

func (b *limitedBuffer) Write(p []byte) (int, error) {
	n := len(p)
	room := outputLimit - b.Len()
	if len(p) > room {
		b.truncated = true
		p = p[:room]
	}
	_, _ = b.Buffer.Write(p)
	return n, nil
}
func (b *limitedBuffer) text() string {
	s := b.String()
	if b.truncated {
		s += "\n[output truncated]"
	}
	return s
}

type nativeProgram struct {
	bin, dir, build string
	maxBytes        int
	timeout         time.Duration
	// metal is the program's kernels as Metal source and launch descriptors
	// (docs/spec/56-kernels.md section 5), nil when it declares none; the
	// runner replays recorded launches on the device with it.
	metal *metal.Result
}
type outcome struct {
	status, signature, output string
	classes                   map[uint32]bool
	trace                     []TraceEvent
	traceTruncated            bool
	commands                  []Command
	// launches are the kernel launches the case recorded through
	// test_launch (docs/spec/110-testing.md, "Launch targets").
	launches []launchRecord
	// got and want are the values a test_check_eq_*/test_check_ne_* failure
	// reported, spelled in the operand type; wantNot marks the "not equal"
	// form. Empty for every other outcome.
	got, want string
	wantNot   bool
}

// failureValues spells the two 64-bit values a fail-values report carries in
// the operand's own type: kind bit 2 reads them as signed, bit 4 as Bool,
// otherwise unsigned; bit 1 marks a "not equal" check.
func failureValues(got, want uint64, kind uint64) (gotText, wantText string, wantNot bool) {
	spell := func(v uint64) string {
		switch {
		case kind&4 != 0:
			if v != 0 {
				return "true"
			}
			return "false"
		case kind&2 != 0:
			return strconv.FormatInt(int64(v), 10)
		default:
			return strconv.FormatUint(v, 10)
		}
	}
	return spell(got), spell(want), kind&1 != 0
}

func buildNative(pkg Package, cfg Config) (*nativeProgram, error) {
	dir, err := os.MkdirTemp("", "oak-test-*")
	if err != nil {
		return nil, err
	}
	keep := false
	defer func() {
		if !keep {
			_ = os.RemoveAll(dir)
		}
	}()
	adapter, err := loadAdapter(cfg.Adapter)
	if err != nil {
		return nil, err
	}
	compilation := packageCompilation(pkg, adapter)
	var kernels *metal.Result
	if emitted, err := compilation.EmitMetal().Get(); err == nil && emitted != nil && len(emitted.Kernels) > 0 {
		kernels = emitted
	}
	generated, err := compilation.EmitC().Get()
	if err != nil {
		return nil, err
	}
	// The manifests' native inputs (`link`, `framework`; docs/spec/83-modules.md
	// section 4.6) link into the test binary exactly as into `oak build`'s.
	inputs, err := compilation.LinkInputs()
	if err != nil {
		return nil, err
	}
	linkArgs, linkIdentity, err := linkArguments(inputs)
	if err != nil {
		return nil, err
	}
	var source strings.Builder
	fmt.Fprintf(&source, "#define OAK_COMMAND_LIMIT %d\n", min(commandLimit, cfg.MaxBytes/commandWidth))
	source.WriteString(nativePreamble)
	source.WriteString("\n#define main oak_test_application_entry\n")
	source.WriteString(generated)
	source.WriteString("\n#undef main\n")
	fmt.Fprintf(&source, `
int main(int argc, char **argv) {
 if (argc != 3) return 120;
 oak_test_report_path = argv[2];
 oak_test_report = fopen(argv[2], "w");
 if (!oak_test_report) return 121;
 unsigned char *data = calloc(%d + 1u, 1u);
 if (!data) return 122;
 size_t size = fread(data, 1, %d + 1u, stdin);
 if (ferror(stdin) || size > %d) return 123;
 switch (strtol(argv[1], NULL, 10)) {
`, cfg.MaxBytes, cfg.MaxBytes, cfg.MaxBytes)
	for i, test := range pkg.Registry {
		fmt.Fprintf(&source, "case %d: oak_test_generating = %d; %s(", i, map[bool]int{true: 1, false: 0}[test.Kind == "generator"], pkg.symbol(test.Name))
		if test.Kind != "unit" && test.Kind != "launch" {
			source.WriteString("(oak_view_u8){data, (u32)size}")
		}
		source.WriteString("); break;\n")
	}
	source.WriteString("default: return 124;\n}\nfputs(\"pass\\n\", oak_test_report);\nfclose(oak_test_report);\nfree(data);\nreturn 0;\n}\n")
	cpath := filepath.Join(dir, "test.c")
	if err := os.WriteFile(cpath, []byte(source.String()), 0600); err != nil {
		return nil, err
	}
	cc, err := exec.LookPath(cfg.CC)
	if err != nil {
		return nil, err
	}
	// -ffp-contract=off keeps floating-point semantics exactly as written
	// (docs/spec/90-backend.md section 7a).
	flags := []string{"-std=c11", "-O1", "-g", "-ffp-contract=off"}
	versionArgs := []string{"--version"}
	if pkg.Target.OS != "" && !pkg.Target.IsHost() {
		// A foreign target compiles through the toolchain `oak build -target`
		// resolves — zig cc, a cross clang, a GNU cross compiler — with the
		// driver's target arguments before the compilation's own; -cc is the
		// host's compiler and does not apply.
		drv, err := toolchain.Resolve(pkg.Target, toolchain.Options{CPU: cfg.CPU}, nil, nil)
		if err != nil {
			return nil, fmt.Errorf("oak test -target %s: %w", pkg.Target, err)
		}
		cc = drv.Path
		flags = append(append([]string{}, drv.Args...), flags...)
		// `zig cc --version`, not `zig --version`: the identity query goes
		// through the driver's own arguments.
		versionArgs = append(append([]string{}, drv.Args...), "--version")
		if drv.Static {
			flags = append(flags, "-static")
		}
	}
	if cfg.Sanitize {
		flags = append(flags, "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer")
	}
	args := append(append([]string{}, flags...), "-o", filepath.Join(dir, "test"), cpath)
	args = append(args, linkArgs...)
	args = append(args, "-lm")
	adapterIdentity := ""
	if adapter != nil {
		adapterIdentity = adapter.identity
		for i, data := range adapter.objects {
			path := filepath.Join(dir, fmt.Sprintf("adapter-%d%s", i, filepath.Ext(adapter.manifest.Objects[i].Path)))
			if err := os.WriteFile(path, data, 0600); err != nil {
				return nil, err
			}
			args = append(args, path)
		}
	}
	ctx, cancel := context.WithTimeout(context.Background(), cfg.BuildTimeout)
	defer cancel()
	version := exec.CommandContext(ctx, cc, versionArgs...)
	version.Dir = dir // any stray output a driver writes lands in the build directory
	var versionOutput limitedBuffer
	version.Stdout, version.Stderr = &versionOutput, &versionOutput
	if err := version.Run(); err != nil {
		return nil, fmt.Errorf("C compiler identity: %w", err)
	}
	// Generated C captures compiler/lowering changes; flags and compiler identity
	// prevent replay under a silently different native build.
	hash := sha256.Sum256([]byte(engineVersion + "\n" + source.String() + "\n" + strings.Join(flags, " ") + "\n" + versionOutput.String() + "\nadapter-v1:" + adapterIdentity + "\nlink-v1:" + linkIdentity))
	// The same identity keys the build cache (docs/spec/115-tooling.md
	// section 3): an unchanged test binary is copied, not recompiled.
	binary := filepath.Join(dir, "test")
	cacheKey := ""
	if identity, err := buildcache.CompilerIdentity(cc); err == nil {
		cacheKey = buildcache.Key("oak-test-v1", hex.EncodeToString(hash[:]), identity)
	}
	cached := false
	if cacheKey != "" {
		if entry, ok := buildcache.Lookup(cacheKey); ok {
			cached = buildcache.Copy(entry, binary) == nil
		}
	}
	if !cached {
		var output limitedBuffer
		cmd := exec.CommandContext(ctx, cc, args...)
		cmd.Dir = dir
		cmd.Stdout, cmd.Stderr = &output, &output
		if err := cmd.Run(); err != nil {
			return nil, fmt.Errorf("C compilation: %w\n%s", err, output.text())
		}
		if cacheKey != "" {
			_ = buildcache.Store(cacheKey, binary)
		}
	}
	keep = true
	return &nativeProgram{bin: filepath.Join(dir, "test"), dir: dir, build: hex.EncodeToString(hash[:]), maxBytes: cfg.MaxBytes, timeout: cfg.Timeout, metal: kernels}, nil
}

// linkArguments spells the manifests' native inputs as C compiler arguments
// and returns an identity covering each object's bytes and each framework's
// name for the build fingerprint (docs/spec/83-modules.md section 4.6). A
// `framework` line links only on macOS and is skipped elsewhere.
func linkArguments(inputs []compiler.LinkInput) ([]string, string, error) {
	var args []string
	var identity strings.Builder
	for _, input := range inputs {
		switch input.Kind {
		case "object":
			data, err := os.ReadFile(input.Path)
			if err != nil {
				return nil, "", fmt.Errorf("link %s: %w", input.Path, err)
			}
			sum := sha256.Sum256(data)
			fmt.Fprintf(&identity, "object %s %x\n", input.Path, sum)
			args = append(args, input.Path)
		case "framework":
			fmt.Fprintf(&identity, "framework %s\n", input.Path)
			if runtime.GOOS == "darwin" {
				args = append(args, "-framework", input.Path)
			}
		}
	}
	return args, identity.String(), nil
}

const nativePreamble = `
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static FILE *oak_test_report;
static const char *oak_test_report_path;
static unsigned oak_test_generating, oak_test_emitted_count;
/* Recorded kernel launches (docs/spec/110-testing.md, "Launch targets"):
   a binary sidecar beside the report, one record per test_launch — the
   kernel and grid, each argument's bytes before the run, each span's
   bytes after — which the runner replays on the device. */
static FILE *oak_test_launches;
static void oak_test_launch_file(void) {
 if (oak_test_launches || !oak_test_report_path) return;
 char path[4096];
 snprintf(path, sizeof path, "%s.launches", oak_test_report_path);
 oak_test_launches = fopen(path, "wb");
}
void oak_test_host_launch_begin(const char *kernel, uint32_t grid) {
 oak_test_launch_file();
 if (oak_test_launches) fprintf(oak_test_launches, "launch %s %u\n", kernel, (unsigned)grid);
}
static void oak_test_launch_bytes(const void *base, uint32_t bytes) {
 if (bytes) fwrite(base, 1, bytes, oak_test_launches);
 fputc('\n', oak_test_launches);
}
void oak_test_host_launch_arg(const char *name, const char *kind, const char *element, const void *base, uint32_t bytes) {
 if (!oak_test_launches) return;
 fprintf(oak_test_launches, "arg %s %s %s %u\n", name, kind, element, (unsigned)bytes);
 oak_test_launch_bytes(base, bytes);
}
void oak_test_host_launch_out(const char *name, const void *base, uint32_t bytes) {
 if (!oak_test_launches) return;
 fprintf(oak_test_launches, "out %s %u\n", name, (unsigned)bytes);
 oak_test_launch_bytes(base, bytes);
}
void oak_test_host_launch_end(void) {
 if (oak_test_launches) { fputs("end\n", oak_test_launches); fflush(oak_test_launches); }
}
uint32_t oak_test_host_command_limit(void) { return OAK_COMMAND_LIMIT; }
void oak_test_host_command(uint32_t kind, uint32_t target, uint32_t value) {
 if (!oak_test_report) exit(125);
 if (!oak_test_generating || oak_test_emitted_count >= OAK_COMMAND_LIMIT) {
  fputs("error command-mode-or-limit\n", oak_test_report); fflush(oak_test_report); exit(125);
 }
 fprintf(oak_test_report, "command %u %u %u\n", (unsigned)kind, (unsigned)target, (unsigned)value);
 oak_test_emitted_count++;
}
static unsigned oak_test_trace_count;
void oak_test_host_trace(uint32_t id, uint64_t a, uint64_t b) {
 if (!oak_test_report) return;
 if (oak_test_trace_count < 256) {
  fprintf(oak_test_report, "trace %u %llu %llu\n", (unsigned)id, (unsigned long long)a, (unsigned long long)b);
  oak_test_trace_count++;
 } else if (oak_test_trace_count == 256) {
  fputs("trace-truncated\n", oak_test_report);
  oak_test_trace_count++;
 }
 fflush(oak_test_report);
}
void oak_test_host_fail(uint32_t id) {
 if (oak_test_report) { fprintf(oak_test_report, "fail %u\n", (unsigned)id); fflush(oak_test_report); }
 exit(101);
}
void oak_test_host_fail_values(uint32_t id, uint64_t got, uint64_t want, uint32_t kind) {
 if (oak_test_report) {
  fprintf(oak_test_report, "fail-values %u %llu %llu %u\n", (unsigned)id, (unsigned long long)got, (unsigned long long)want, (unsigned)kind);
  fflush(oak_test_report);
 }
 exit(101);
}
void oak_test_host_discard(void) {
 if (oak_test_report) { fputs("discard\n", oak_test_report); fflush(oak_test_report); }
 exit(102);
}
void oak_test_host_classify(uint32_t id) {
 if (oak_test_report) { fprintf(oak_test_report, "class %u\n", (unsigned)id); fflush(oak_test_report); }
}
`

func (p *nativeProgram) run(index int, input []byte) (result outcome) {
	result = outcome{status: "fail", classes: map[uint32]bool{}}
	if len(input) > p.maxBytes {
		result.signature = "harness:input-too-large"
		return result
	}
	// One report file per execution: workers run cases concurrently.
	reportFile, err := os.CreateTemp(p.dir, "report-*")
	if err != nil {
		result.signature = "harness:report-file"
		result.output = err.Error()
		return result
	}
	reportPath := reportFile.Name()
	_ = reportFile.Close()
	defer os.Remove(reportPath)
	defer os.Remove(reportPath + ".launches")
	ctx, cancel := context.WithTimeout(context.Background(), p.timeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, p.bin, strconv.Itoa(index), reportPath)
	cmd.Stdin = bytes.NewReader(input)
	var output limitedBuffer
	cmd.Stdout, cmd.Stderr = &output, &output
	// Bound pipe draining too: a descendant must not keep the runner waiting.
	cmd.WaitDelay = 100 * time.Millisecond
	err = cmd.Run()
	result.output = output.text()
	timedOut := ctx.Err() != nil
	// Read the flushed prefix even when a watchdog killed the process. A
	// partial final report line must not hide the original timeout outcome.
	defer func() {
		if timedOut {
			result.status, result.signature = "fail", "timeout"
		}
	}()
	var report []byte
	if f, openErr := os.Open(reportPath); openErr == nil {
		report, _ = io.ReadAll(io.LimitReader(f, outputLimit+1))
		_ = f.Close()
	}
	if len(report) > outputLimit {
		result.signature = "harness:report-limit"
		return result
	}
	if launches, launchErr := readLaunches(reportPath + ".launches"); launchErr != nil {
		result.signature = "harness:bad-launch-record"
		result.output += launchErr.Error()
		return result
	} else {
		result.launches = launches
	}
	terminal := ""
	for _, line := range strings.Split(strings.TrimSpace(string(report)), "\n") {
		fields := strings.Fields(line)
		if len(fields) == 0 {
			continue
		}
		if len(fields) == 2 && fields[0] == "error" {
			result.signature = "harness:" + fields[1]
			return result
		} else if len(fields) == 4 && fields[0] == "command" {
			kind, e1 := strconv.ParseUint(fields[1], 10, 32)
			target, e2 := strconv.ParseUint(fields[2], 10, 32)
			value, e3 := strconv.ParseUint(fields[3], 10, 32)
			if e1 != nil || e2 != nil || e3 != nil || len(result.commands) >= min(commandLimit, p.maxBytes/commandWidth) {
				result.signature = "harness:bad-command-report"
				return result
			}
			result.commands = append(result.commands, Command{Kind: uint32(kind), Target: uint32(target), Value: uint32(value)})
		} else if len(fields) == 4 && fields[0] == "trace" {
			id, e1 := strconv.ParseUint(fields[1], 10, 32)
			a, e2 := strconv.ParseUint(fields[2], 10, 64)
			b, e3 := strconv.ParseUint(fields[3], 10, 64)
			if e1 != nil || e2 != nil || e3 != nil || len(result.trace) >= traceLimit || result.traceTruncated {
				result.signature = "harness:bad-report"
				return result
			}
			result.trace = append(result.trace, TraceEvent{ID: uint32(id), A: a, B: b})
		} else if len(fields) == 1 && fields[0] == "trace-truncated" {
			if len(result.trace) != traceLimit || result.traceTruncated {
				result.signature = "harness:bad-report"
				return result
			}
			result.traceTruncated = true
		} else if len(fields) == 5 && fields[0] == "fail-values" {
			_, e1 := strconv.ParseUint(fields[1], 10, 32)
			got, e2 := strconv.ParseUint(fields[2], 10, 64)
			want, e3 := strconv.ParseUint(fields[3], 10, 64)
			kind, e4 := strconv.ParseUint(fields[4], 10, 32)
			if e1 != nil || e2 != nil || e3 != nil || e4 != nil || kind > 7 {
				result.signature = "harness:bad-report"
				return result
			}
			terminal = "fail"
			result.signature = "invariant:" + fields[1]
			result.got, result.want, result.wantNot = failureValues(got, want, kind)
		} else if len(fields) == 2 && (fields[0] == "class" || fields[0] == "fail") {
			id, e := strconv.ParseUint(fields[1], 10, 32)
			if e != nil {
				result.signature = "harness:bad-report"
				return result
			}
			if fields[0] == "class" {
				result.classes[uint32(id)] = true
			} else {
				terminal = "fail"
				result.signature = "invariant:" + fields[1]
			}
		} else if len(fields) == 1 && (fields[0] == "pass" || fields[0] == "discard") {
			terminal = fields[0]
		} else {
			result.signature = "harness:bad-report"
			return result
		}
	}
	if err == nil && terminal == "pass" {
		result.status = "pass"
		return result
	}
	if exit, ok := err.(*exec.ExitError); ok {
		if exit.ExitCode() == 102 && terminal == "discard" {
			result.status = "discard"
			return result
		}
		if exit.ExitCode() == 101 && terminal == "fail" {
			return result
		}
		result.signature = "exit:" + exit.ProcessState.String()
		return result
	}
	result.signature = "harness:missing-result"
	if err != nil {
		result.output += "\n" + err.Error()
	}
	return result
}
