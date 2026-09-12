package compiler

import (
	"runtime"
	"strings"
	"testing"
)

// Process spawning from Oak (docs/spec/92-ffi.md sections 2.5.6 and 2.5.7,
// ml roadmap D4): c.argv_of(bytes, slots) forms a NUL-terminated pointer
// vector over strings the program terminated itself, c.out(x) hands a
// foreign call the address of a local for the call's extent, and c.null()
// spells the optional pointer arguments. Executed against libc posix_spawn
// and waitpid: /bin/echo exits 0, /usr/bin/false exits 1.
const spawnHelpers = `
posix_spawn: (pid: c.Ptr, path: c.String, actions: c.Ptr, attr: c.Ptr, argv: c.Ptr, envp: c.Ptr): c.Int = c.extern("posix_spawn")
waitpid: (pid: c.Int, status: c.Ptr, options: c.Int): c.Int = c.extern("waitpid")

// run_and_wait spawns path with the NUL-terminated arguments in args and an
// empty environment, then returns the child's exit code; a spawn error is
// 1000 + errno, a wait mismatch 2000.
run_and_wait: (path: []u8, args: []u8): u32 {
  slot_storage: [8]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  env_storage: [1]c.Ptr
  env_slots: [*]c.Ptr = span(&env_storage)
  no_env: [0]u8
  empty: []u8 = view(&no_env)
  pid: c.Int = c.Int(i32(0))
  status: c.Int = c.Int(i32(0))
  spawned: c.Int = posix_spawn(c.out(pid), c.cstr(path), c.null(), c.null(), c.argv_of(args, slots), c.argv_of(empty, env_slots))
  i32(spawned) != i32(0) ? { u32(1000) + u32_bits_i32(i32(spawned)) } | {
    waited: c.Int = waitpid(pid, c.out(status), c.Int(i32(0)))
    i32(waited) != i32(pid) ? { u32(2000) } | { (u32_bits_i32(i32(status)) >> u32(8)) & u32(255) }
  }
}
`

func skipWithoutPosixSpawn(t *testing.T) {
	t.Helper()
	if runtime.GOOS != "darwin" && runtime.GOOS != "linux" {
		t.Skip("posix_spawn test needs a POSIX host with /bin/echo and /usr/bin/false")
	}
}

func TestE2ESpawnEchoAndFalse(t *testing.T) {
	skipWithoutPosixSpawn(t)
	src := spawnHelpers + `
main: (): i32 {
  // "/bin/echo\0" with argv "echo\0" "d4\0"
  echo_path: [10]u8 = [10]u8{ 47, 98, 105, 110, 47, 101, 99, 104, 111, 0 }
  echo_args: [8]u8 = [8]u8{ 101, 99, 104, 111, 0, 100, 52, 0 }
  path: []u8 = view(&echo_path)
  args: []u8 = view(&echo_args)
  assert(run_and_wait(path, args) == u32(0))
  // "/usr/bin/false\0" with argv "false\0" exits 1
  false_path: [15]u8 = [15]u8{ 47, 117, 115, 114, 47, 98, 105, 110, 47, 102, 97, 108, 115, 101, 0 }
  false_args: [6]u8 = [6]u8{ 102, 97, 108, 115, 101, 0 }
  fpath: []u8 = view(&false_path)
  fargs: []u8 = view(&false_args)
  assert(run_and_wait(fpath, fargs) == u32(1))
  42
}
`
	stdout, code, abnormal := buildAndRunFrom(t, "ffi_spawn", New().WithSource("ffi_spawn.oak", src))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v) stdout=%q", code, abnormal, stdout)
	}
	if !strings.Contains(stdout, "d4") {
		t.Fatalf("the spawned echo did not write its argument: stdout=%q", stdout)
	}
}

// The argument vector's checks run at the call: strings that do not end in
// NUL, or too few pointer slots, trap before any pointer reaches C.
func TestE2EArgvChecksTrap(t *testing.T) {
	skipWithoutPosixSpawn(t)
	cases := map[string]string{
		"unterminated": `
main: (): i32 {
  slot_storage: [4]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  env_storage: [1]c.Ptr
  env_slots: [*]c.Ptr = span(&env_storage)
  no_env: [0]u8
  empty: []u8 = view(&no_env)
  bad: [4]u8 = [4]u8{ 101, 99, 104, 111 }
  args: []u8 = view(&bad)
  pid: c.Int = c.Int(i32(0))
  r: c.Int = posix_spawn(c.out(pid), c.cstr("/bin/echo\0"), c.null(), c.null(), c.argv_of(args, slots), c.argv_of(empty, env_slots))
  i32(r)
}
`,
		"too few slots": `
main: (): i32 {
  slot_storage: [2]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  env_storage: [1]c.Ptr
  env_slots: [*]c.Ptr = span(&env_storage)
  no_env: [0]u8
  empty: []u8 = view(&no_env)
  three: [6]u8 = [6]u8{ 97, 0, 98, 0, 99, 0 }
  args: []u8 = view(&three)
  pid: c.Int = c.Int(i32(0))
  r: c.Int = posix_spawn(c.out(pid), c.cstr("/bin/echo\0"), c.null(), c.null(), c.argv_of(args, slots), c.argv_of(empty, env_slots))
  i32(r)
}
`,
	}
	for name, body := range cases {
		t.Run(name, func(t *testing.T) {
			_, code, abnormal := buildAndRunFrom(t, "ffi_argv_trap", New().WithSource("ffi_argv_trap.oak", spawnHelpers+body))
			if !abnormal && code == 0 {
				t.Fatalf("expected the argument vector check to trap, got a clean exit")
			}
		})
	}
}

// The forms are checked where they stand: a c.Ptr parameter, named operands
// of the right shapes, a local of a c.* scalar or boundary struct for
// c.out, and never outside an extern call.
func TestArgvAndOutRejections(t *testing.T) {
	cases := []struct {
		name string
		src  string
		code string
		want string
	}{
		{
			name: "argv operand must be a []u8 view",
			src: `
f: (argv: c.Ptr): c.Int = c.extern("f")
main: (): i32 {
  words: [2]u32 = [2]u32{ 1, 2 }
  w: []u32 = view(&words)
  slot_storage: [2]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  i32(f(c.argv_of(w, slots)))
}
`,
			code: "OAK-F0111",
			want: "read-only view []u8",
		},
		{
			name: "argv slots must be a [*]c.Ptr span",
			src: `
f: (argv: c.Ptr): c.Int = c.extern("f")
main: (): i32 {
  bytes: [2]u8 = [2]u8{ 97, 0 }
  b: []u8 = view(&bytes)
  slot_storage: [2]u64
  slots: [*]u64 = span(&slot_storage)
  i32(f(c.argv_of(b, slots)))
}
`,
			code: "OAK-F0111",
			want: "writable span [*]c.Ptr",
		},
		{
			name: "argv must stand for a c.Ptr parameter",
			src: `
f: (n: c.Int): c.Int = c.extern("f")
main: (): i32 {
  bytes: [2]u8 = [2]u8{ 97, 0 }
  b: []u8 = view(&bytes)
  slot_storage: [2]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  i32(f(c.argv_of(b, slots)))
}
`,
			code: "OAK-F0111",
			want: "c.Ptr",
		},
		{
			name: "out operand must be a c.* scalar or boundary struct",
			src: `
f: (p: c.Ptr): c.Int = c.extern("f")
main: (): i32 {
  n: u32 = 0
  i32(f(c.out(n)))
}
`,
			code: "OAK-F0112",
			want: "c.* scalar",
		},
		{
			name: "out rejects an opaque pointer",
			src: `
f: (p: c.Ptr): c.Int = c.extern("f")
main: (): i32 {
  p: c.Ptr = c.null()
  i32(f(c.out(p)))
}
`,
			code: "OAK-F0112",
			want: "opaque",
		},
		{
			name: "out rejects a global",
			src: `
f: (p: c.Ptr): c.Int = c.extern("f")
counter: c.Int = c.Int(i32(0))
main: (): i32 = i32(f(c.out(counter)))
`,
			code: "OAK-F0112",
			want: "global",
		},
		{
			name: "out must stand for a c.Ptr parameter",
			src: `
f: (n: c.Int): c.Int = c.extern("f")
main: (): i32 {
  x: c.Int = c.Int(i32(0))
  i32(f(c.out(x)))
}
`,
			code: "OAK-F0112",
			want: "c.Ptr",
		},
		{
			name: "argv is not an expression",
			src: `
main: (): i32 {
  bytes: [2]u8 = [2]u8{ 97, 0 }
  b: []u8 = view(&bytes)
  slot_storage: [2]c.Ptr
  slots: [*]c.Ptr = span(&slot_storage)
  p: c.Ptr = c.argv_of(b, slots)
  0
}
`,
			code: "OAK-F0103",
			want: "not an expression",
		},
		{
			name: "out is only an argument to an extern",
			src: `
g: (p: c.Ptr): u32 = 1
main: (): i32 {
  x: c.Int = c.Int(i32(0))
  i32_bits_u32(g(c.out(x)))
}
`,
			code: "OAK-F0103",
			want: "only an argument to an extern binding",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, err := New().WithSource("reject.oak", tc.src).EmitC().Get()
			if err == nil {
				t.Fatalf("expected a diagnostic")
			}
			if !strings.Contains(err.Error(), tc.code) || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("want %s with %q, got %v", tc.code, tc.want, err)
			}
		})
	}
}

// c.out is a write of its local for the borrow checker: the call sees the
// binding's storage, so the value read back afterwards is the callee's.
// Exercised through waitpid above; here the accepted struct shape is a
// boundary struct with fixed-width fields, checked to compile and run
// against gettimeofday's timeval on POSIX hosts.
func TestE2EOutStructParameter(t *testing.T) {
	skipWithoutPosixSpawn(t)
	src := `
Timeval: type = struct { sec: i64, usec: i64 }
gettimeofday: (tv: c.Ptr, tz: c.Ptr): c.Int = c.extern("gettimeofday")

main: (): i32 {
  tv: Timeval = Timeval { sec: i64(0), usec: i64(0) }
  r: c.Int = gettimeofday(c.out(tv), c.null())
  assert(i32(r) == i32(0))
  // After 2001-09-09 and before 2286-11-20 in seconds; microseconds in range.
  assert(tv.sec > i64(1000000000) && tv.sec < i64(10000000000))
  assert(tv.usec >= i64(0) && tv.usec < i64(1000000))
  42
}
`
	_, code, abnormal := buildAndRunFrom(t, "ffi_out_struct", New().WithSource("ffi_out_struct.oak", src))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
