# Endian integer encoding

Status: normative. The qualified package and scalar reference implementation
are stabilizing; target-specific load/store realizations are future work.

## 1. Scope and API

`endian` encodes fixed-width integers in caller-owned byte storage without
allocation, host-byte-order assumptions, alignment requirements, or unsafe
pointer conversion.

```oak
import("endian")

pub Error: type = | BufferTooSmall

pub read_u16_le: (src: []u8, offset: u32): Result[u16, Error]
pub write_u16_le: (dst: [*]u8, offset: u32, value: u16): Result[u32, Error]
```

The package provides the same read/write pair for `u16`, `u32`, and `u64`, in
both little-endian (`_le`) and big-endian (`_be`) order. There is no generic
runtime byte-order value: order and width are visible in the call and specialize
to straight-line code.

## 2. Semantics and failure

A read returns the unsigned integer whose bytes at `[offset, offset + width)`
have the named order. A successful write replaces exactly that range and
returns `Ok(width)`; the count is not the next offset.

Every operation first calls `bytes.range_fits(len(storage), offset, width)`.
An offset beyond the end or an incomplete range returns
`Err(BufferTooSmall)`. No byte is read or written on failure, and failed writes
leave the complete destination unchanged. In particular, the maximum `u32`
offset is rejected without forming a wrapping `offset + width` expression.

The functions perform exactly width byte accesses after one constant-time
guard, use O(1) auxiliary storage, do not allocate, and have no I/O, blocking,
global state, synchronization, or callbacks. They make no constant-time
side-channel claim beyond fixed work for a selected width.

## 3. Portability and optimization

The scalar definitions are valid on little- or big-endian machines, with
strict alignment, 32- or 64-bit pointers, no heap, and no libc. The package is
therefore freestanding on hosted macOS/Linux, Oak OS, and STM32-class targets.
It encodes integers only; it does not define record layout, checksums,
persistence ordering, or transaction framing.

A backend may replace a scalar sequence with an aligned or unaligned target
load/store only after establishing equivalence to the extracted definition:
the same complete-range guard, byte order, value, returned width, failure, and
destination frame. Target capability and alignment selection remain internal;
the portable signature does not expose an architecture ABI.

## 4. Evidence and remaining work

- **Implemented:** `stdlib/endian.oak`, depending only on `bytes`; legacy
  `bytes_read_*` and `bytes_write_*` names are derived for `import(std)`.
- **Tested:** `compiler/e2e_stdlib_endian_package_test.go` executes all twelve
  operations through the interpreter and C backend, checks exact bytes,
  boundary preservation, hostile-offset rejection, failure atomicity,
  flat-surface agreement, namespace isolation, and allocator absence. The
  older differential test compares the flat spellings with Go's
  `encoding/binary` over additional values and boundary positions.
- **Modeled:** `spec/lean/Oak/Stdlib/EndianExtracted.lean` is generated from the
  checked Oak package and held by the extraction drift test.
- **Proved:** `EndianLaws.lean` proves every rejected write preserves arbitrary
  destination storage, rejected reads return `BufferTooSmall`, and fixes
  representative little- and big-endian decoding results.
- **Refined:** not yet; scalar-to-target-load/store correspondence is the next
  proof-directed performance increment.

Universal read/write round trips and exact successful destination-frame
theorems remain open before a target-specific implementation is admitted.
