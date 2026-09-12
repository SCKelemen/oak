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
	"sync"
	"syscall"
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
	// resident runs cases through resident harness workers (nativeServe);
	// idle holds the workers not running a case, workers every one alive.
	resident bool
	mu       sync.Mutex
	idle     []*residentWorker
	workers  map[*residentWorker]bool
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
	fmt.Fprintf(&source, "#define OAK_COMMAND_LIMIT %d\n#define OAK_MAX_BYTES %d\n#define OAK_OUTPUT_LIMIT %d\n", min(commandLimit, cfg.MaxBytes/commandWidth), cfg.MaxBytes, outputLimit)
	source.WriteString(nativePreamble)
	source.WriteString("\n#define main oak_test_application_entry\n")
	source.WriteString(generated)
	source.WriteString("\n#undef main\n")
	source.WriteString(`
static int oak_test_case(long index, const char *report_path, unsigned char *data, size_t size) {
 oak_test_report_path = report_path;
 oak_test_report = fopen(report_path, "w");
 if (!oak_test_report) return 121;
 switch (index) {
`)
	for i, test := range pkg.Registry {
		fmt.Fprintf(&source, "case %d: oak_test_generating = %d; %s(", i, map[bool]int{true: 1, false: 0}[test.Kind == "generator"], pkg.symbol(test.Name))
		if test.Kind != "unit" && test.Kind != "launch" {
			source.WriteString("(oak_view_u8){data, (u32)size}")
		}
		source.WriteString("); break;\n")
	}
	source.WriteString("default: return 124;\n}\nfputs(\"pass\\n\", oak_test_report);\nfclose(oak_test_report);\nreturn 0;\n}\n")
	source.WriteString(nativeServe)
	source.WriteString(`
int main(int argc, char **argv) {
#ifndef _WIN32
 if (argc == 2 && strcmp(argv[1], "serve") == 0) return oak_test_serve();
#endif
 if (argc != 3) return 120;
 unsigned char *data = calloc(OAK_MAX_BYTES + 1u, 1u);
 if (!data) return 122;
 size_t size = fread(data, 1, OAK_MAX_BYTES + 1u, stdin);
 if (ferror(stdin) || size > OAK_MAX_BYTES) return 123;
 int code = oak_test_case(strtol(argv[1], NULL, 10), argv[2], data, size);
 free(data);
 return code;
}
`)
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
	// Resident workers fork per case, which the host's own harness supports
	// everywhere but Windows; a cross-built harness runs one process per
	// case as before.
	resident := cfg.Resident && residentSupported && (pkg.Target.OS == "" || pkg.Target.IsHost())
	return &nativeProgram{bin: filepath.Join(dir, "test"), dir: dir, build: hex.EncodeToString(hash[:]), maxBytes: cfg.MaxBytes, timeout: cfg.Timeout, metal: kernels, resident: resident, workers: map[*residentWorker]bool{}}, nil
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

// nativeServe is the harness's resident mode (docs/spec/110-testing.md,
// "Resident workers"): started once as `test serve`, the process reads case
// records from stdin — index, report path and input bytes, each length
// checked before it is read — and runs every case in a fresh fork of
// itself, so a case sees exactly the state a new process would, while the
// process start-up and the sanitizer runtime's initialization are paid
// once per worker instead of once per case. The child's output is drained
// into the same bound the per-process path applies; the reply carries the
// wait status, the output, and whether it was truncated. The parent uses
// read and write, never stdio, so the child inherits no buffered bytes.
const nativeServe = `
#include <string.h>
#ifndef _WIN32
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
static int oak_test_read_exact(int fd, void *buf, size_t n) {
 unsigned char *p = (unsigned char *)buf;
 while (n) {
  ssize_t r = read(fd, p, n);
  if (r < 0) { if (errno == EINTR) continue; return 0; }
  if (r == 0) return 0;
  p += r; n -= (size_t)r;
 }
 return 1;
}
static int oak_test_write_all(int fd, const void *buf, size_t n) {
 const unsigned char *p = (const unsigned char *)buf;
 while (n) {
  ssize_t w = write(fd, p, n);
  if (w < 0) { if (errno == EINTR) continue; return 0; }
  p += w; n -= (size_t)w;
 }
 return 1;
}
static int oak_test_serve(void) {
 unsigned char *out = malloc(OAK_OUTPUT_LIMIT);
 unsigned char *data = malloc(OAK_MAX_BYTES + 1u);
 char *path = malloc(4097);
 if (!out || !data || !path) return 122;
 for (;;) {
  uint32_t header[3];
  if (!oak_test_read_exact(0, header, sizeof header)) return 0;
  if (header[1] == 0 || header[1] > 4096 || header[2] > OAK_MAX_BYTES) return 123;
  if (!oak_test_read_exact(0, path, header[1])) return 123;
  path[header[1]] = 0;
  if (header[2] && !oak_test_read_exact(0, data, header[2])) return 123;
  int pipefd[2];
  if (pipe(pipefd) != 0) return 126;
  fflush(NULL);
  pid_t pid = fork();
  if (pid < 0) return 126;
  if (pid == 0) {
   close(pipefd[0]);
   if (dup2(pipefd[1], 1) < 0 || dup2(pipefd[1], 2) < 0) _exit(126);
   close(pipefd[1]);
   int devnull = open("/dev/null", O_RDONLY);
   if (devnull < 0 || dup2(devnull, 0) < 0) _exit(126);
   close(devnull);
   exit(oak_test_case((long)header[0], path, data, header[2]));
  }
  close(pipefd[1]);
  size_t got = 0;
  uint32_t flags = 0;
  for (;;) {
   unsigned char sink[4096];
   ssize_t r = read(pipefd[0], sink, sizeof sink);
   if (r < 0) { if (errno == EINTR) continue; break; }
   if (r == 0) break;
   size_t room = OAK_OUTPUT_LIMIT - got;
   if ((size_t)r > room) { memcpy(out + got, sink, room); got += room; flags |= 1u; }
   else { memcpy(out + got, sink, (size_t)r); got += (size_t)r; }
  }
  close(pipefd[0]);
  int status = 0;
  while (waitpid(pid, &status, 0) < 0) { if (errno != EINTR) return 126; }
  uint32_t reply[4];
  reply[0] = WIFSIGNALED(status) ? 1u : 0u;
  reply[1] = WIFSIGNALED(status) ? (uint32_t)WTERMSIG(status) : (uint32_t)WEXITSTATUS(status);
  reply[2] = (uint32_t)got;
#ifdef WCOREDUMP
  if (WIFSIGNALED(status) && WCOREDUMP(status)) flags |= 2u;
#endif
  reply[3] = flags;
  if (!oak_test_write_all(1, reply, sizeof reply) || (got && !oak_test_write_all(1, out, got))) return 126;
 }
}
#endif
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
	var status exitStatus
	var timedOut bool
	if p.resident {
		status, result.output, timedOut = p.runResident(index, input, reportPath)
	} else {
		ctx, cancel := context.WithTimeout(context.Background(), p.timeout)
		defer cancel()
		cmd := exec.CommandContext(ctx, p.bin, strconv.Itoa(index), reportPath)
		cmd.Stdin = bytes.NewReader(input)
		var output limitedBuffer
		cmd.Stdout, cmd.Stderr = &output, &output
		// Bound pipe draining too: a descendant must not keep the runner waiting.
		cmd.WaitDelay = 100 * time.Millisecond
		status = statusOf(cmd.Run())
		result.output = output.text()
		timedOut = ctx.Err() != nil
	}
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
	if status.passed() && terminal == "pass" {
		result.status = "pass"
		return result
	}
	if status.ran && !status.passed() {
		if status.exited && status.code == 102 && terminal == "discard" {
			result.status = "discard"
			return result
		}
		if status.exited && status.code == 101 && terminal == "fail" {
			return result
		}
		result.signature = "exit:" + status.String()
		return result
	}
	result.signature = "harness:missing-result"
	if status.err != nil {
		result.output += "\n" + status.err.Error()
	}
	return result
}

// exitStatus is how a case's process ended, the same for a process the
// runner started and for a fork a resident worker reported.
type exitStatus struct {
	ran    bool // the process ran to an end: exited or killed by a signal
	exited bool
	code   int
	signal syscall.Signal
	core   bool
	err    error // when !ran: why it did not
}

func (s exitStatus) passed() bool { return s.ran && s.exited && s.code == 0 }

// String spells the status as os.ProcessState does, so signatures are the
// same on both paths.
func (s exitStatus) String() string {
	text := ""
	switch {
	case s.exited:
		text = "exit status " + strconv.Itoa(s.code)
	default:
		text = "signal: " + s.signal.String()
	}
	if s.core {
		text += " (core dumped)"
	}
	return text
}

// statusOf reads a finished exec.Cmd's error.
func statusOf(err error) exitStatus {
	if err == nil {
		return exitStatus{ran: true, exited: true}
	}
	exit, ok := err.(*exec.ExitError)
	if !ok {
		return exitStatus{err: err}
	}
	ws, ok := exit.Sys().(syscall.WaitStatus)
	if !ok {
		return exitStatus{ran: true, exited: true, code: exit.ExitCode()}
	}
	if ws.Signaled() {
		return exitStatus{ran: true, signal: ws.Signal(), core: ws.CoreDump()}
	}
	return exitStatus{ran: true, exited: true, code: ws.ExitStatus()}
}
