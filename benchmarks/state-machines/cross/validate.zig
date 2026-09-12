// Zig standard library: std.unicode.utf8ValidateSlice over the shared input.
// The file is read through libc so the harness does not track Zig's
// changing std.fs surface; build with -lc.
const std = @import("std");
const c = struct {
    extern "c" fn fopen(path: [*:0]const u8, mode: [*:0]const u8) ?*anyopaque;
    extern "c" fn fread(buf: [*]u8, size: usize, n: usize, f: *anyopaque) usize;
    extern "c" fn fseek(f: *anyopaque, off: c_long, whence: c_int) c_int;
    extern "c" fn ftell(f: *anyopaque) c_long;
    extern "c" fn fclose(f: *anyopaque) c_int;
    extern "c" fn malloc(n: usize) ?[*]u8;
    const timespec = extern struct { sec: c_long, nsec: c_long };
    extern "c" fn clock_gettime(clk: c_int, ts: *timespec) c_int;
    fn now_ns() u64 {
        var ts: timespec = undefined;
        _ = clock_gettime(6, &ts); // CLOCK_MONOTONIC on macOS
        return @as(u64, @intCast(ts.sec)) * 1_000_000_000 + @as(u64, @intCast(ts.nsec));
    }
};
pub fn main() !void {
    const f = c.fopen("input.bin", "rb") orelse return error.NoInput;
    _ = c.fseek(f, 0, 2);
    const n: usize = @intCast(c.ftell(f));
    _ = c.fseek(f, 0, 0);
    const raw = c.malloc(n + 64) orelse return error.OutOfMemory;
    if (c.fread(raw, 1, n, f) != n) return error.ShortRead;
    _ = c.fclose(f);
    const buf = raw[0..n];
    var best: u64 = std.math.maxInt(u64);
    var ok = false;
    var r: usize = 0;
    while (r < 5) : (r += 1) {
        const t0 = c.now_ns();
        ok = std.unicode.utf8ValidateSlice(buf);
        const t = c.now_ns() - t0;
        if (t < best) best = t;
    }
    const nf: f64 = @floatFromInt(n);
    const b: f64 = @floatFromInt(best);
    std.debug.print("{s:<34} {d:6.2} ns/byte  {d:6.2} GB/s\n", .{ "Zig std.unicode.utf8ValidateSlice", b / nf, nf / b });
    if (!ok) std.process.exit(1);
}
