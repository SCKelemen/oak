const View32 = extern struct { base: [*]const u32, len: u32 };
const View64 = extern struct { base: [*]const u64, len: u32 };

// The caller supplies len initialized, aligned elements; sums wrap modulo 2^N.
export fn zig_sum32(v: View32) u32 {
    var acc: u32 = 0;
    var i: u32 = 0;
    while (i < v.len) : (i += 1) acc +%= v.base[i];
    return acc;
}

export fn zig_sum64(v: View64) u64 {
    var acc: u64 = 0;
    var i: u32 = 0;
    while (i < v.len) : (i += 1) acc +%= v.base[i];
    return acc;
}
