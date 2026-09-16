// Command exact_fma measures contraction separately from compiler coverage.
// It never changes the source contract or turns on implicit contraction.
package main

import (
	_ "embed"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
)

//go:embed fixture/kernels.oak
var source string

//go:embed fixture/runner.c
var runner string

//go:embed fixture/maps.oak
var mapSource string

//go:embed fixture/map_runner.c
var mapRunner string

type sample struct {
	Backend      string  `json:"backend"`
	Width        int     `json:"width"`
	Form         string  `json:"form"`
	Round        int     `json:"round"`
	Elapsed      uint64  `json:"elapsed_ns"`
	Bits         string  `json:"bits"`
	NSPerElement float64 `json:"ns_per_element"`
}

type body struct {
	Backend   string      `json:"backend"`
	Name      string      `json:"name"`
	Verdict   string      `json:"verdict"`
	Frame     int64       `json:"frame_bytes"`
	CodeBytes int         `json:"code_bytes"`
	Assembly  string      `json:"assembly"`
	Message   string      `json:"verdict_message"`
	Metrics   opt.Metrics `json:"metrics"`
}

type report struct {
	Workload   string   `json:"workload"`
	Revision   string   `json:"revision"`
	Dirty      bool     `json:"dirty_worktree"`
	Date       string   `json:"date"`
	Host       string   `json:"host"`
	LoadBefore string   `json:"load_before"`
	LoadAfter  string   `json:"load_after"`
	CC         string   `json:"cc"`
	Flags      []string `json:"flags"`
	Elements   int      `json:"elements"`
	Calls      int      `json:"calls"`
	Bodies     []body   `json:"native_bodies"`
	Samples    []sample `json:"samples"`
}

func capture(command string, args ...string) string {
	output, err := exec.Command(command, args...).CombinedOutput()
	if err != nil {
		return fmt.Sprintf("unavailable: %v", err)
	}
	return strings.TrimSpace(string(output))
}

func run() error {
	cc := flag.String("cc", "cc", "C compiler")
	elements := flag.Int("n", 4096, "elements per call (1..2^24)")
	calls := flag.Int("calls", 4096, "calls per sample (1..2^20)")
	rounds := flag.Int("samples", 9, "interleaved samples per variant (1..100)")
	out := flag.String("out", "", "new JSON report path; default stdout")
	workload := flag.String("workload", "dot", "dot or map")
	flag.Parse()
	if *workload != "dot" && *workload != "map" {
		return fmt.Errorf("unknown workload %q", *workload)
	}
	program, harness := source, runner
	if *workload == "map" {
		program, harness = mapSource, mapRunner
	}
	if *elements < 1 || *elements > 1<<24 || *calls < 1 || *calls > 1<<20 || *rounds < 1 || *rounds > 100 {
		return fmt.Errorf("benchmark arguments out of bounds")
	}
	if runtime.GOARCH != "arm64" || runtime.GOOS != "darwin" {
		return fmt.Errorf("initial performance experiment requires an ARM64 macOS host")
	}
	build, err := os.MkdirTemp("", "oak-exact-fma-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(build)
	result := report{Revision: capture("git", "rev-parse", "HEAD"), Date: time.Now().UTC().Format(time.RFC3339), Host: capture("sysctl", "-n", "machdep.cpu.brand_string"), CC: capture(*cc, "--version"), Elements: *elements, Calls: *calls, Flags: []string{"-std=c11", "-O3", "-ffp-contract=off", "-fno-fast-math"}}
	result.Workload = *workload
	result.Dirty = capture("git", "status", "--porcelain") != ""
	// Do not let inherited experimental filters silently change the coverage.
	for _, key := range []string{"OAK_NATIVE_ONLY", "OAK_OPT_SKIP", "OAK_OPT_BEAM", "OAK_NATIVE_DUMP"} {
		if err := os.Unsetenv(key); err != nil {
			return err
		}
	}
	backends := []string{"c", "native-identity", "native-no-maps", "native-optimized"}
	executables := make([]string, len(backends))
	for index, backend := range backends {
		dir := filepath.Join(build, backend)
		if err := os.Mkdir(dir, 0700); err != nil {
			return err
		}
		comp := compiler.New().WithSource("exact_fma.oak", program)
		var text string
		var object []byte
		if backend == "c" {
			text, err = comp.EmitC().Get()
		} else {
			var skipped []string
			if backend == "native-identity" {
				for _, transform := range nativegen.Transforms() {
					skipped = append(skipped, transform.Name())
				}
			} else if backend == "native-no-maps" {
				skipped = []string{nativegen.TransformVectorMaps}
			}
			if err := os.Setenv("OAK_OPT_SKIP", strings.Join(skipped, ",")); err != nil {
				return err
			}
			comp = comp.WithNativeBodies().WithNativeAsm()
			model, checkErr := comp.Check().Get()
			if checkErr != nil {
				return checkErr
			}
			seen := 0
			for _, function := range model.AsmFunctions {
				if !strings.HasPrefix(function.Name, *workload) {
					continue
				}
				verdict := model.NativeVerdicts[function.Name]
				if verdict.Kind != asm.VerdictProven && verdict.Kind != asm.VerdictWitnessed {
					return fmt.Errorf("%s %s: %s (%s)", backend, function.Name, verdict.Kind, verdict.Message)
				}
				code, _, encodeErr := asm.EncodeFunction(function)
				if encodeErr != nil {
					return encodeErr
				}
				result.Bodies = append(result.Bodies, body{Backend: backend, Name: function.Name, Verdict: verdict.Kind.String(), Frame: function.Frame, CodeBytes: len(code), Assembly: nativegen.Describe(function), Message: verdict.Message, Metrics: nativegen.Metrics(function)})
				seen++
			}
			if seen != 4 {
				return fmt.Errorf("%s: got %d native dot bodies, want 4", backend, seen)
			}
			native, emitErr := comp.EmitNative(compiler.HostObjectFormat()).Get()
			if emitErr != nil {
				return emitErr
			}
			text, object = native.C, native.Object
		}
		if err != nil {
			return err
		}
		for name, content := range map[string][]byte{"kernels.c": []byte(text), "runner.c": []byte(harness), "kernels.o": object} {
			if err := os.WriteFile(filepath.Join(dir, name), content, 0600); err != nil {
				return err
			}
		}
		executable := filepath.Join(dir, "runner")
		args := append([]string{}, result.Flags...)
		args = append(args, "-I"+dir, filepath.Join(dir, "runner.c"))
		if backend != "c" {
			args = append(args, filepath.Join(dir, "kernels.o"))
		}
		args = append(args, "-lm", "-o", executable)
		if output, err := exec.Command(*cc, args...).CombinedOutput(); err != nil {
			return fmt.Errorf("%s build: %w\n%s", backend, err, output)
		}
		executables[index] = executable
	}
	result.LoadBefore = capture("uptime")
	checksums := map[int]string{}
	for round := 0; round < *rounds; round++ {
		// Rotate all backend/width/form combinations, retaining their
		// actual observation order rather than sorting samples by elapsed time.
		for offset := 0; offset < 4*len(backends); offset++ {
			index := observationIndex(round, offset, len(backends))
			backend, width, form := index/4, 32+32*((index%4)/2), index%2+1
			output, err := exec.Command(executables[backend], strconv.Itoa(width), strconv.Itoa(form), strconv.Itoa(*elements), strconv.Itoa(*calls)).CombinedOutput()
			if err != nil {
				return fmt.Errorf("sample %s f%d form %d: %w\n%s", backends[backend], width, form, err, output)
			}
			var measured sample
			if err := json.Unmarshal(output, &measured); err != nil {
				return err
			}
			if err := acceptSample(measured, width, checksums); err != nil {
				return err
			}
			measured.Backend, measured.Width, measured.Round = backends[backend], width, round
			measured.Form = []string{"strict", "fused"}[form-1]
			measured.NSPerElement = float64(measured.Elapsed) / float64(*elements) / float64(*calls)
			result.Samples = append(result.Samples, measured)
		}
	}
	result.LoadAfter = capture("uptime")
	writer := os.Stdout
	if *out != "" {
		writer, err = os.OpenFile(*out, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0600)
		if err != nil {
			return err
		}
		defer writer.Close()
	}
	encoder := json.NewEncoder(writer)
	encoder.SetIndent("", "  ")
	return encoder.Encode(result)
}

func observationIndex(round, offset, backends int) int {
	return (round + offset) % (4 * backends)
}

func acceptSample(measured sample, width int, checksums map[int]string) error {
	if measured.Elapsed == 0 || len(measured.Bits) != 16 {
		return fmt.Errorf("invalid timing/checksum: %+v", measured)
	}
	if _, err := strconv.ParseUint(measured.Bits, 16, 64); err != nil {
		return fmt.Errorf("invalid checksum: %w", err)
	}
	if previous, ok := checksums[width]; ok && previous != measured.Bits {
		return fmt.Errorf("f%d checksum mismatch: %s vs %s", width, previous, measured.Bits)
	}
	checksums[width] = measured.Bits
	return nil
}

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
