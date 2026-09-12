package testrunner

import (
	"bufio"
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"io"
	"math"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/SCKelemen/oak/codegen/metal"
	"github.com/SCKelemen/oak/codegen/metal/gpu"
)

// Launch targets (docs/spec/110-testing.md, "Launch targets"): a test
// declares kernel launches with test_launch; the harness runs each on the
// host — the C realization — and records it (the kernel, the grid, every
// argument's bytes before, every span's bytes after) in a binary sidecar.
// The runner replays each record on this machine's GPU through the
// framework's run-time compiler (codegen/metal/gpu) and compares the spans
// and the fault word: the two realizations must agree bit for bit.

// launchRecord is one recorded test_launch.
type launchRecord struct {
	Kernel string
	Grid   uint32
	Args   []launchArg
}

// launchArg is one recorded argument: the descriptor's name and kind, the
// element type, the bytes before the launch, and for a span the bytes after.
type launchArg struct {
	Name, Kind, Element string
	In, Out             []byte
}

// launchLimit bounds one sidecar: 64 MiB of recorded buffers.
const launchLimit = 64 << 20

// readLaunches parses the sidecar a test case wrote; a missing file is no
// launches.
func readLaunches(path string) ([]launchRecord, error) {
	f, err := os.Open(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil, nil
		}
		return nil, err
	}
	defer f.Close()
	r := bufio.NewReaderSize(io.LimitReader(f, launchLimit+1), 1<<16)
	var launches []launchRecord
	var current *launchRecord
	total := 0
	readBytes := func(n uint64) ([]byte, error) {
		total += int(n)
		if total > launchLimit {
			return nil, fmt.Errorf("recorded launches exceed %d bytes", launchLimit)
		}
		data := make([]byte, n)
		if _, err := io.ReadFull(r, data); err != nil {
			return nil, fmt.Errorf("short launch record: %v", err)
		}
		if nl, err := r.ReadByte(); err != nil || nl != '\n' {
			return nil, fmt.Errorf("launch record bytes not terminated")
		}
		return data, nil
	}
	for {
		line, err := r.ReadString('\n')
		if err == io.EOF && line == "" {
			break
		}
		if err != nil && err != io.EOF {
			return nil, err
		}
		fields := strings.Fields(line)
		if len(fields) == 0 {
			continue
		}
		switch {
		case fields[0] == "launch" && len(fields) == 3:
			grid, err := strconv.ParseUint(fields[2], 10, 32)
			if err != nil {
				return nil, fmt.Errorf("launch grid: %v", err)
			}
			launches = append(launches, launchRecord{Kernel: fields[1], Grid: uint32(grid)})
			current = &launches[len(launches)-1]
		case fields[0] == "arg" && len(fields) == 5 && current != nil:
			n, err := strconv.ParseUint(fields[4], 10, 32)
			if err != nil {
				return nil, fmt.Errorf("launch arg size: %v", err)
			}
			data, err := readBytes(n)
			if err != nil {
				return nil, err
			}
			current.Args = append(current.Args, launchArg{Name: fields[1], Kind: fields[2], Element: fields[3], In: data})
		case fields[0] == "out" && len(fields) == 3 && current != nil:
			n, err := strconv.ParseUint(fields[2], 10, 32)
			if err != nil {
				return nil, fmt.Errorf("launch out size: %v", err)
			}
			data, err := readBytes(n)
			if err != nil {
				return nil, err
			}
			found := false
			for i := range current.Args {
				if current.Args[i].Name == fields[1] {
					current.Args[i].Out = data
					found = true
				}
			}
			if !found {
				return nil, fmt.Errorf("launch out %s names no argument", fields[1])
			}
		case fields[0] == "end" && current != nil:
			current = nil
		default:
			return nil, fmt.Errorf("malformed launch record line %q", strings.TrimSpace(line))
		}
	}
	if current != nil {
		return nil, fmt.Errorf("unterminated launch record")
	}
	return launches, nil
}

// replayLaunches runs every recorded launch on the device and compares it
// with the host's record. It returns the device's name and, on the first
// divergence, a failure text naming the launch, the span, and the element.
func replayLaunches(ctx context.Context, kernels *metal.Result, launches []launchRecord) (device string, failure string, err error) {
	if len(launches) == 0 {
		return "", "", nil
	}
	if reason := gpu.Available(); reason != "" {
		return "skipped: " + reason, "", nil
	}
	device, err = gpu.Device()
	if err != nil {
		return "", "", err
	}
	if kernels == nil {
		return device, "", fmt.Errorf("the package declares no kernels, yet a launch was recorded")
	}
	for i, launch := range launches {
		var desc *metal.Kernel
		for k := range kernels.Kernels {
			if kernels.Kernels[k].Name == launch.Kernel {
				desc = &kernels.Kernels[k]
			}
		}
		if desc == nil {
			return device, "", fmt.Errorf("launch %d: kernel %s is not in the emitted Metal", i+1, launch.Kernel)
		}
		args := map[string]gpu.Arg{}
		for _, a := range launch.Args {
			args[a.Name] = gpu.Arg(a.In)
		}
		runCtx, cancel := context.WithTimeout(ctx, 2*time.Minute)
		result, runErr := gpu.Run(runCtx, kernels.Source, *desc, launch.Grid, args)
		cancel()
		if runErr != nil {
			return device, "", fmt.Errorf("launch %d of %s: %v", i+1, launch.Kernel, runErr)
		}
		if result.Fault != 0 {
			return device, fmt.Sprintf("launch %d of %s: the device raised fault %d where the host ran through", i+1, launch.Kernel, result.Fault), nil
		}
		for _, a := range launch.Args {
			if a.Kind != "span" {
				continue
			}
			got := result.Spans[a.Name]
			if !bytes.Equal(got, a.Out) {
				return device, describeDivergence(i+1, launch.Kernel, a, got), nil
			}
		}
	}
	return device, "", nil
}

// describeDivergence names the first differing element of a span, spelled
// in the element type.
func describeDivergence(launch int, kernel string, a launchArg, got []byte) string {
	size, known := gpu.ElementSize(a.Element)
	if !known || size == 0 {
		size = 1
	}
	if len(got) != len(a.Out) {
		return fmt.Sprintf("launch %d of %s: span %s has %d bytes on the device, %d on the host", launch, kernel, a.Name, len(got), len(a.Out))
	}
	for i := 0; i+size <= len(got); i += size {
		if !bytes.Equal(got[i:i+size], a.Out[i:i+size]) {
			return fmt.Sprintf("launch %d of %s: span %s element %d: device %s, host %s", launch, kernel, a.Name, i/size, spellElement(a.Element, got[i:i+size]), spellElement(a.Element, a.Out[i:i+size]))
		}
	}
	return fmt.Sprintf("launch %d of %s: span %s differs", launch, kernel, a.Name)
}

func spellElement(element string, b []byte) string {
	switch element {
	case "f32":
		return strconv.FormatFloat(float64(math.Float32frombits(binary.LittleEndian.Uint32(b))), 'g', -1, 32)
	case "u8", "Bool":
		return strconv.FormatUint(uint64(b[0]), 10)
	case "i8":
		return strconv.FormatInt(int64(int8(b[0])), 10)
	case "u16":
		return strconv.FormatUint(uint64(binary.LittleEndian.Uint16(b)), 10)
	case "i16":
		return strconv.FormatInt(int64(int16(binary.LittleEndian.Uint16(b))), 10)
	case "u32":
		return strconv.FormatUint(uint64(binary.LittleEndian.Uint32(b)), 10)
	case "i32":
		return strconv.FormatInt(int64(int32(binary.LittleEndian.Uint32(b))), 10)
	case "u64":
		return strconv.FormatUint(binary.LittleEndian.Uint64(b), 10)
	case "i64":
		return strconv.FormatInt(int64(binary.LittleEndian.Uint64(b)), 10)
	}
	return fmt.Sprintf("%x", b)
}
