#![no_std]

#[repr(C)]
pub struct View32 { base: *const u32, len: u32 }
#[repr(C)]
pub struct View64 { base: *const u64, len: u32 }

// The caller supplies len initialized, aligned elements; sums wrap modulo 2^N.
#[no_mangle]
pub unsafe extern "C" fn rust_sum32(v: View32) -> u32 {
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < v.len {
        acc = acc.wrapping_add(*v.base.add(i as usize));
        i += 1;
    }
    acc
}

#[no_mangle]
pub unsafe extern "C" fn rust_sum64(v: View64) -> u64 {
    let mut acc = 0u64;
    let mut i = 0u32;
    while i < v.len {
        acc = acc.wrapping_add(*v.base.add(i as usize));
        i += 1;
    }
    acc
}
