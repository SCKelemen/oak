package compiler

import (
	"strings"
	"testing"
)

// Lanes (docs/spec/56-kernels.md section 2a; the ml pilot's F1, increment
// (a)): lane(G) is the thread's place in its group, a store indexed by it
// is the lane's own slot, and the footprint gid * G + lane(G) is the tile
// shape. On the host the body runs once per lane per position.
const kernelLanesProgram = `package main

kernel scale: (gid: u32, x: []f32, out: [*]f32): () = {
  i: u32 = gid * 4 + lane(4)
  i < len(out) && i < len(x) ? { out[i] = x[i] * 2.0 }
}

main: (): i32 = {
  xs: [8]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  ys: [8]f32 = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
  g: u32 = 0
  while g < 2 {
    scale(g, view(&xs), span(&ys))
    g = g + 1
  }
  ys[0] == 2.0 && ys[3] == 8.0 && ys[4] == 10.0 && ys[7] == 16.0 ? 42 | 1
}
`

func TestE2EKernelLanes(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelLanesProgram})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	src := result.Source
	for _, want := range []string{
		"threadgroup 4",
		"kernel void scale(uint gid [[threadgroup_position_in_grid]], uint oak_lid [[thread_position_in_threadgroup]]",
		"uint i = ((gid * 4u) + oak_lid);",
		"out[i] = (x[i] * 2.0f);",
	} {
		if !strings.Contains(src, want) {
			t.Fatalf("missing %q in:\n%s", want, src)
		}
	}
	if strings.Contains(src, "if (oak_lid == 0u) { out[") {
		t.Fatalf("a lane-indexed store is not guarded to one thread:\n%s", src)
	}
	if k := kernelNamed(t, result, "scale"); k.Independence != "tile 4" || k.Threadgroup != 4 {
		t.Fatalf("descriptor = %+v", k)
	}
}

// Threadgroup memory and barriers (increment (b)): a (threadgroup) array
// is one per group, barrier() separates phases, and a local declared
// before a barrier and read after it is private to its lane. The host runs
// the phases lane by lane and agrees with the device.
const kernelArenaProgram = `package main

kernel reverse_blocks: (gid: u32, x: []f32, out: [*]f32): () = {
  tile: [4]f32 (threadgroup)
  i: u32 = gid * 4 + lane(4)
  v: f32 = 0.0
  i < len(x) ? {
    tile[lane(4)] = x[i]
    v = x[i] * 10.0
  }
  barrier()
  i < len(out) ? { out[i] = tile[3 - lane(4)] + v }
}

main: (): i32 = {
  xs: [8]f32 = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  ys: [8]f32 = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
  g: u32 = 0
  while g < 2 {
    reverse_blocks(g, view(&xs), span(&ys))
    g = g + 1
  }
  // block 0 reversed is [4 3 2 1] plus 10 * [1 2 3 4]: [14 23 32 41]; block 1: [8 7 6 5] + [50 60 70 80].
  ys[0] == 14.0 && ys[1] == 23.0 && ys[3] == 41.0 && ys[4] == 58.0 && ys[7] == 85.0 ? 42 | 1
}
`

func TestE2EKernelArenaBarrier(t *testing.T) {
	root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": kernelArenaProgram})
	if code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root)); abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreted: %d", got)
	}
	result, err := New().WithPackageDir(root).EmitMetal().Get()
	if err != nil {
		t.Fatal(err)
	}
	src := result.Source
	for _, want := range []string{
		"  threadgroup float tile[4];",
		"threadgroup_barrier(mem_flags::mem_threadgroup);",
		"tile[oak_check(oak_lid, 4u, oak_fault)] = x[i];",
		"out[i] = (tile[oak_check((3u - oak_lid), 4u, oak_fault)] + v);",
	} {
		if !strings.Contains(src, want) {
			t.Fatalf("missing %q in:\n%s", want, src)
		}
	}
	// The host form: phases as lane loops, the arena and the private local
	// declared once per position.
	emitted, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"oak_lane", "oak_priv_v"} {
		if !strings.Contains(emitted, want) {
			t.Fatalf("missing %q in the C:\n%s", want, emitted)
		}
	}
}

// The placement rules (OAK-K0101).
func TestKernelLaneRejections(t *testing.T) {
	for name, c := range map[string][2]string{
		"lane in a helper":      {"helper: (): u32 = lane(4)\nkernel k: (gid: u32, out: [*]f32): () = {\n  i: u32 = gid * 4 + helper()\n  i < len(out) ? { out[i] = 1.0 }\n}\n", "belongs to a kernel body"},
		"barrier in a loop":     {"kernel k: (gid: u32, out: [*]f32): () = {\n  i: u32 = gid * 4 + lane(4)\n  k2: u32 = 0\n  while k2 < 2 {\n    barrier()\n    k2 = k2 + 1\n  }\n  i < len(out) ? { out[i] = 1.0 }\n}\n", "top level"},
		"two group sizes":       {"kernel k: (gid: u32, out: [*]f32): () = {\n  i: u32 = gid * 4 + lane(4)\n  j: u32 = lane(8)\n  i + j < len(out) ? { out[i] = 1.0 }\n}\n", "one group size"},
		"arena without a group": {"kernel k: (gid: u32, out: [*]f32): () = {\n  tile: [4]f32 (threadgroup)\n  gid < len(out) ? { out[gid] = tile[0] }\n}\n", "declares its group through lane(G)"},
		"unannotated private":   {"kernel k: (gid: u32, x: []f32, out: [*]f32): () = {\n  i: u32 = gid * 4 + lane(4)\n  v := x[0]\n  barrier()\n  i < len(out) ? { out[i] = v }\n}\n", "needs a type annotation"},
		"lane past the tile":    {"kernel k: (gid: u32, out: [*]f32): () = {\n  i: u32 = gid * 8 + lane(4)\n  i < len(out) ? { out[i] = 1.0 }\n}\n", "positions could overlap"},
	} {
		src := "package main\n\n" + c[0] + "\nmain: (): i32 = 0\n"
		root := writeModule(t, map[string]string{"oak.mod": helloManifest, "main.oak": src})
		_, err := New().WithPackageDir(root).EmitMetal().Get()
		if err == nil || !strings.Contains(err.Error(), c[1]) {
			t.Fatalf("%s: want %q, got %v", name, c[1], err)
		}
	}
}
