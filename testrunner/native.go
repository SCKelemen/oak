package testrunner

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
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
}
type outcome struct {
	status, signature, output string
	classes                   map[uint32]bool
	trace                     []TraceEvent
	traceTruncated            bool
	commands                  []Command
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
	generated, err := packageCompilation(pkg, adapter).EmitC().Get()
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
		if test.Kind != "unit" {
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
	flags := []string{"-std=c11", "-O1", "-g"}
	if cfg.Sanitize {
		flags = append(flags, "-fsanitize=address,undefined", "-fno-sanitize-recover=all", "-fno-omit-frame-pointer")
	}
	args := append(append([]string{}, flags...), "-o", filepath.Join(dir, "test"), cpath)
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
	var output limitedBuffer
	cmd := exec.CommandContext(ctx, cc, args...)
	cmd.Stdout, cmd.Stderr = &output, &output
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("C compilation: %w\n%s", err, output.text())
	}
	version := exec.CommandContext(ctx, cc, "--version")
	var versionOutput limitedBuffer
	version.Stdout, version.Stderr = &versionOutput, &versionOutput
	if err := version.Run(); err != nil {
		return nil, fmt.Errorf("C compiler identity: %w", err)
	}
	// Generated C captures compiler/lowering changes; flags and compiler identity
	// prevent replay under a silently different native build.
	hash := sha256.Sum256([]byte(engineVersion + "\n" + source.String() + "\n" + strings.Join(flags, " ") + "\n" + versionOutput.String() + "\nadapter-v1:" + adapterIdentity))
	keep = true
	return &nativeProgram{bin: filepath.Join(dir, "test"), dir: dir, build: hex.EncodeToString(hash[:]), maxBytes: cfg.MaxBytes, timeout: cfg.Timeout}, nil
}

const nativePreamble = `
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static FILE *oak_test_report;
static unsigned oak_test_generating, oak_test_emitted_count;
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
	reportPath := filepath.Join(p.dir, "report")
	_ = os.Remove(reportPath)
	ctx, cancel := context.WithTimeout(context.Background(), p.timeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, p.bin, strconv.Itoa(index), reportPath)
	cmd.Stdin = bytes.NewReader(input)
	var output limitedBuffer
	cmd.Stdout, cmd.Stderr = &output, &output
	// Bound pipe draining too: a descendant must not keep the runner waiting.
	cmd.WaitDelay = 100 * time.Millisecond
	err := cmd.Run()
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
