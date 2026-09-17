package compiler

import (
	"context"
	"encoding/binary"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/codegen/metal/gpu"
)

// Ask 5.25: every lane stores successive elements in its own row, without
// making every lane walk the entire row. The incomplete tail is untouched.
const kernelStridedStoresProgram = `
kernel strided: (gid: u32, out: [*]u32, cols: u32): () = {
  s: u32 = 0
  while s < cols / 4 {
    out[gid * cols + s * 4 + lane(4)] = gid * 100 + s * 4 + lane(4) + 1
    s = s + 1
  }
}
kernel aliased: (gid: u32, out: [*]u32, cols: u32): () = {
  base: u32 = cols * gid
  l: u32 = lane(4)
  s: u32 = 0
  while s < cols / 4 {
    offset: u32 = l + 4 * s
    i: u32 = offset + base
    i < len(out) ? { out[i] = gid * 100 + offset + 1 }
    s = s + 1
  }
}
main: (): i32 = {
  a: [40]u32
  b: [40]u32
  cols: u32 = 0
  while cols < 14 {
    j: u32 = 0
    while j < 40 {
      a[j] = 999
      b[j] = 999
      j = j + 1
    }
    g: u32 = 0
    while g < 3 {
      strided(g, span(&a), cols)
      aliased(g, span(&b), cols)
      g = g + 1
    }
    h: u32 = 0
    while h < 3 {
      k: u32 = 0
      while k < cols {
        want: u32 = k < (cols / 4) * 4 ? h * 100 + k + 1 | 999
        assert(a[h * cols + k] == want)
        assert(b[h * cols + k] == want)
        k = k + 1
      }
      h = h + 1
    }
    // No row may spill into the following one or beyond the launch.
    assert(a[3 * cols] == 999 && b[3 * cols] == 999)
    cols = cols + 1
  }
  42
}
`

func TestE2EKernelStridedStores(t *testing.T) {
	code, abnormal := buildAndRun(t, "strided_stores", kernelStridedStoresProgram)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretChecked(t, kernelStridedStoresProgram); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
}

func TestKernelStridedIndependence(t *testing.T) {
	for name, index := range map[string]string{
		"left associated": "gid * 12 + s * 4 + lane(4)",
		"parenthesized":   "gid * 12 + (s * 4 + lane(4))",
		"reordered":       "lane(4) + (4 * s + 12 * gid)",
	} {
		t.Run(name, func(t *testing.T) {
			src := `kernel k: (gid: u32, out: [*]u32): () = {
  s: u32 = 0
  while s < 12 / 4 {
    out[` + index + `] = lane(4)
    s = s + 1
  }
}
main: (): i32 = 0
`
			result, err := New().WithSource("strided.oak", src).EmitMetal().Get()
			if err != nil {
				t.Fatal(err)
			}
			if k := result.Kernels[0]; k.Independence != "tile 12" || k.Threadgroup != 4 {
				t.Fatalf("descriptor = %+v", k)
			}
			if strings.Contains(result.Source, "if (oak_lid == 0u)") {
				t.Fatal("a lane-strided store was reduced to lane 0")
			}
		})
	}
}

func TestKernelStridedIndependenceRejections(t *testing.T) {
	base := `kernel k: (gid: u32, out: [*]u32, cols: u32, other: u32): () = {
  l: u32 = lane(4)
  s: u32 = 0
  while s < cols / 4 {
    out[gid * cols + s * 4 + l] = l
    s = s + 1
  }
}
main: (): i32 = 0
`
	for name, change := range map[string][2]string{
		"wrong stride":                 {"s * 4 + l", "s * 8 + l"},
		"wrong divisor":                {"cols / 4", "cols / 2"},
		"different row size":           {"cols / 4", "other / 4"},
		"unbounded offset":             {"cols / 4", "cols"},
		"extra offset":                 {"s * 4 + l", "s * 4 + l + 1"},
		"counter changed before store": {"out[gid", "s = s + 1\n    out[gid"},
		"mutable lane alias":           {"s: u32 = 0", "l = l + 4\n  s: u32 = 0"},
		"mutable row size":             {"s: u32 = 0", "cols = cols + 4\n  s: u32 = 0"},
		"mutable offset alias": {"out[gid * cols + s * 4 + l] = l",
			"offset: u32 = s * 4 + l\n    offset = offset + cols\n    out[gid * cols + offset] = l"},
		"offset without loop fact": {"s: u32 = 0", "s: u32 = 0\n  out[gid * cols + s * 4 + l] = l"},
		"span read across rows":    {"= l\n    s =", "= out[gid * cols + s * 4 + l + 1]\n    s ="},
	} {
		t.Run(name, func(t *testing.T) {
			src := strings.Replace(base, change[0], change[1], 1)
			_, err := New().WithSource("strided_rejected.oak", src).EmitC().Get()
			if err == nil || !strings.Contains(err.Error(), CodeKernelIndependence) {
				t.Fatalf("want %s, got %v", CodeKernelIndependence, err)
			}
		})
	}
}

func TestE2EKernelStridedStoresOnDevice(t *testing.T) {
	if reason := gpu.Available(); reason != "" {
		t.Skip(reason)
	}
	ctx, cancel := context.WithTimeout(context.Background(), time.Minute)
	defer cancel()
	result := emitKernels(t, "package main\n"+kernelStridedStoresProgram)
	for _, name := range []string{"strided", "aliased"} {
		k := kernelNamed(t, result, name)
		if k.Independence != "tile cols" || k.Threadgroup != 4 {
			t.Fatalf("descriptor = %+v", k)
		}
		for cols := uint32(0); cols < 14; cols++ {
			out := make(gpu.Arg, 40*4)
			for i := 0; i < 40; i++ {
				binary.LittleEndian.PutUint32(out[4*i:], 999)
			}
			res, err := gpu.Run(ctx, result.Source, k, 3, map[string]gpu.Arg{"out": out, "cols": u32arg(cols)})
			if err != nil {
				t.Fatalf("%s cols=%d: %v", name, cols, err)
			}
			if res.Fault != 0 {
				t.Fatalf("%s cols=%d: fault %d", name, cols, res.Fault)
			}
			data := res.Spans["out"]
			if len(data) != len(out) {
				t.Fatalf("%s: output has %d bytes, want %d", name, len(data), len(out))
			}
			for i := uint32(0); i < 40; i++ {
				want := uint32(999)
				if cols != 0 && i < 3*cols && i%cols < cols/4*4 {
					want = i/cols*100 + i%cols + 1
				}
				if got := binary.LittleEndian.Uint32(data[4*i:]); got != want {
					t.Fatalf("%s cols=%d index=%d: got %d, want %d", name, cols, i, got, want)
				}
			}
		}
	}
}
