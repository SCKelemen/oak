// Package gpu runs Oak's emitted Metal kernels on this machine's GPU
// device (docs/spec/56-kernels.md section 9). The Metal framework ships
// with macOS and compiles shader source at run time, so no Xcode toolchain
// is needed: a small Objective-C runner (runner.m.txt, an .m the go tool would otherwise refuse), built once with the
// system C compiler, compiles the source on the device, binds buffers by
// the kernel's launch descriptor, dispatches, and writes the spans and the
// fault word back. Where the runner cannot be built or there is no device,
// Available says why and callers skip.
package gpu

import (
	"context"
	"crypto/sha256"
	_ "embed"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"sync"

	"github.com/SCKelemen/oak/codegen/metal"
)

//go:embed runner.m.txt
var runnerSource string

var (
	once        sync.Once
	runnerPath  string
	unavailable string
)

// Available reports why kernels cannot run on this machine's device, or ""
// when they can: macOS, a C compiler, the Metal framework, and a device.
func Available() string {
	once.Do(build)
	return unavailable
}

// Runner is the path of the built runner, for tools that invoke it.
func Runner() (string, error) {
	if reason := Available(); reason != "" {
		return "", fmt.Errorf("%s", reason)
	}
	return runnerPath, nil
}

func build() {
	if runtime.GOOS != "darwin" {
		unavailable = "Metal kernels run on macOS only"
		return
	}
	cc, err := exec.LookPath("cc")
	if err != nil {
		unavailable = "no C compiler on the path"
		return
	}
	base, err := os.UserCacheDir()
	if err != nil {
		base = os.TempDir()
	}
	sum := sha256.Sum256([]byte(runnerSource))
	dir := filepath.Join(base, "oak", "metal-runner-"+hex.EncodeToString(sum[:8]))
	binary := filepath.Join(dir, "oak_metal_run")
	if _, err := os.Stat(binary); err != nil {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			unavailable = fmt.Sprintf("cannot create %s: %v", dir, err)
			return
		}
		source := filepath.Join(dir, "runner.m")
		if err := os.WriteFile(source, []byte(runnerSource), 0o644); err != nil {
			unavailable = fmt.Sprintf("cannot write the runner source: %v", err)
			return
		}
		cmd := exec.Command(cc, "-fobjc-arc", "-framework", "Metal", "-framework", "Foundation", "-O1", "-o", binary, source)
		if out, err := cmd.CombinedOutput(); err != nil {
			unavailable = fmt.Sprintf("the Metal runner does not build (%v):\n%s", err, strings.TrimSpace(string(out)))
			return
		}
	}
	out, err := exec.Command(binary, "--probe").CombinedOutput()
	if err != nil {
		unavailable = fmt.Sprintf("no Metal device: %s", strings.TrimSpace(string(out)))
		return
	}
	runnerPath = binary
}

// Device names the GPU the runner uses.
func Device() (string, error) {
	runner, err := Runner()
	if err != nil {
		return "", err
	}
	out, err := exec.Command(runner, "--probe").Output()
	return strings.TrimSpace(string(out)), err
}

// Check compiles the emitted Metal source on the device and returns the
// driver's errors, if any.
func Check(ctx context.Context, source string) error {
	runner, err := Runner()
	if err != nil {
		return err
	}
	dir, err := os.MkdirTemp("", "oak-metal-check-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(dir)
	path := filepath.Join(dir, "kernels.metal")
	if err := os.WriteFile(path, []byte(source), 0o644); err != nil {
		return err
	}
	out, err := exec.CommandContext(ctx, runner, "--check", path).CombinedOutput()
	if err != nil {
		return fmt.Errorf("%s", strings.TrimSpace(string(out)))
	}
	return nil
}

// Arg is one kernel argument by parameter name: the bytes of a view or a
// span (element count = len / element size), or of one scalar.
type Arg []byte

// Result is what a launch returns: every span's bytes after the run, and
// the fault word (docs/spec/56-kernels.md section 3; 0 is no fault).
type Result struct {
	Spans map[string][]byte
	Fault uint32
}

// ElementSize is the byte size of a kernel element or scalar type.
func ElementSize(element string) (int, bool) {
	switch element {
	case "u8", "i8", "Bool":
		return 1, true
	case "u16", "i16":
		return 2, true
	case "u32", "i32", "f32":
		return 4, true
	case "u64", "i64":
		return 8, true
	}
	return 0, false
}

type bufferSpec struct {
	Index  int    `json:"index"`
	Kind   string `json:"kind"`
	Path   string `json:"path,omitempty"`
	Out    string `json:"out,omitempty"`
	Count  uint32 `json:"count,omitempty"`
	Length int    `json:"length,omitempty"`
}

type manifest struct {
	Source      string       `json:"source"`
	Kernel      string       `json:"kernel"`
	Threads     uint64       `json:"threads"`
	Threadgroup int64        `json:"threadgroup"`
	Buffers     []bufferSpec `json:"buffers"`
}

// Run launches kernel k of source on the device over grid positions with
// the given arguments — one per view, span, and scalar parameter, by name
// — and returns the spans and the fault word. A group kernel dispatches
// grid * Threadgroup threads in threadgroups of Threadgroup, as the launch
// descriptor states.
func Run(ctx context.Context, source string, k metal.Kernel, grid uint32, args map[string]Arg) (Result, error) {
	runner, err := Runner()
	if err != nil {
		return Result{}, err
	}
	dir, err := os.MkdirTemp("", "oak-metal-run-")
	if err != nil {
		return Result{}, err
	}
	defer os.RemoveAll(dir)
	m := manifest{Source: filepath.Join(dir, "kernels.metal"), Kernel: k.Name, Threads: uint64(grid), Threadgroup: k.Threadgroup}
	if k.Threadgroup > 0 {
		m.Threads = uint64(grid) * uint64(k.Threadgroup)
	}
	if err := os.WriteFile(m.Source, []byte(source), 0o644); err != nil {
		return Result{}, err
	}
	outputs := map[string]string{}
	for i, p := range k.Params {
		switch p.Kind {
		case "grid", "group":
			continue
		}
		arg, given := args[p.Name]
		if !given {
			return Result{}, fmt.Errorf("kernel %s: no argument for parameter %s", k.Name, p.Name)
		}
		size, known := ElementSize(p.Element)
		if !known {
			return Result{}, fmt.Errorf("kernel %s: parameter %s has element %s, which the runner does not size", k.Name, p.Name, p.Element)
		}
		path := filepath.Join(dir, fmt.Sprintf("arg%d.bin", i))
		if err := os.WriteFile(path, []byte(arg), 0o644); err != nil {
			return Result{}, err
		}
		switch p.Kind {
		case "view", "span":
			if len(arg)%size != 0 {
				return Result{}, fmt.Errorf("kernel %s: parameter %s: %d bytes is not a whole number of %s", k.Name, p.Name, len(arg), p.Element)
			}
			spec := bufferSpec{Index: p.Buffers[0], Kind: "data", Path: path, Length: len(arg)}
			if p.Kind == "span" {
				spec.Out = filepath.Join(dir, fmt.Sprintf("out%d.bin", i))
				outputs[p.Name] = spec.Out
			}
			m.Buffers = append(m.Buffers, spec, bufferSpec{Index: p.Buffers[1], Kind: "len", Count: uint32(len(arg) / size)})
		case "scalar":
			if len(arg) != size {
				return Result{}, fmt.Errorf("kernel %s: scalar %s takes %d bytes, got %d", k.Name, p.Name, size, len(arg))
			}
			m.Buffers = append(m.Buffers, bufferSpec{Index: p.Buffers[0], Kind: "scalar", Path: path})
		default:
			return Result{}, fmt.Errorf("kernel %s: parameter %s has kind %s", k.Name, p.Name, p.Kind)
		}
	}
	faultOut := filepath.Join(dir, "fault.bin")
	m.Buffers = append(m.Buffers, bufferSpec{Index: k.Fault, Kind: "fault", Out: faultOut, Length: 4})
	encoded, err := json.Marshal(m)
	if err != nil {
		return Result{}, err
	}
	manifestPath := filepath.Join(dir, "launch.json")
	if err := os.WriteFile(manifestPath, encoded, 0o644); err != nil {
		return Result{}, err
	}
	if out, err := exec.CommandContext(ctx, runner, manifestPath).CombinedOutput(); err != nil {
		return Result{}, fmt.Errorf("metal runner: %v: %s", err, strings.TrimSpace(string(out)))
	}
	result := Result{Spans: map[string][]byte{}}
	for name, path := range outputs {
		data, err := os.ReadFile(path)
		if err != nil {
			return Result{}, err
		}
		result.Spans[name] = data
	}
	fault, err := os.ReadFile(faultOut)
	if err != nil {
		return Result{}, err
	}
	if len(fault) >= 4 {
		result.Fault = binary.LittleEndian.Uint32(fault)
	}
	return result, nil
}
