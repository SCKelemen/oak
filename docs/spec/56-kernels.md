# Kernels

**Status: implemented (first increment), 2026-09-12.** The ml pilot's
request F1 (`docs/notes/ml-language-requests-2026-09.md`): kernels as Oak
functions in a strict subset, compiled by Oak to Metal and to C, so that
the emitted kernel is code a proof can name rather than a string the
runtime assembles.

A kernel is a function. It is declared with the `kernel` marker, its first
parameter is its position in the launch grid, its body lies in the **kernel
subset** (section 2), and it has three realizations that agree:

- the **C backend** compiles it as an ordinary function, so a host loop
  over grid positions computes the launch on the CPU (the `oak run` and
  `oak test` realization);
- the **Metal emitter** (`codegen/metal`, `oak build -metal out.metal`)
  compiles it to a compute kernel with a launch descriptor the host binds
  by (section 3);
- the **Lean extraction** (`95-extraction.md`) states it as a definition,
  the same one for both.

The compiler holds every kernel to the subset in every build, Metal
requested or not (`OAK-K01xx`), so a kernel that compiles is one all three
realizations accept.

## 1. Declaration

```oak
clamp_relu: (x: f32): f32 = x < 0.0 ? 0.0 | x

kernel relu: (gid: u32, x: []f32, y: [*]f32): () = {
  gid < len(y) ? { y[gid] = clamp_relu(x[gid]) }
}

kernel axpy: (gid: u32, a: f32, x: []f32, y: [*]f32, tile: u32): () = {
  base: u32 = gid * tile
  k: u32 = 0
  while k < tile {
    i: u32 = base + k
    i < len(y) ? { y[i] = a * x[i] + y[i] }
    k = k + 1
  }
}
```

`kernel` is contextual: `kernel := 1` and `kernel: u32 = 1` stay ordinary
bindings. The marker applies to the function declaration that follows,
which may be `pub`. Rules:

- The **first parameter is the grid position**, a `u32`, by definition:
  the launch runs the body once per position in `0 .. grid`. The C
  realization is exactly `relu(g, view(&xs), span(&ys))` for each `g`.
- Other parameters are **buffers** — views `[]T` (read) and spans `[*]T`
  (read and write) of a scalar `T` — or **scalars**. Scalars are `u8`
  through `u64`, `i8` through `i64`, `f32`, and `Bool`. `f64` is outside
  the subset (Apple GPUs have no double precision); records, fixed arrays,
  strings, and ADTs are outside this increment.
- The result is `()`: results leave through spans.
- The body is in the kernel subset (section 2). A kernel calls **helpers**
  — ordinary functions in the subset — and never another kernel.

A kernel is otherwise a function: the interpreter runs it, `oak test` tests
it, the extraction states it, effects and forbids apply to it.

## 2. The kernel subset

The Metal emitter is the definition of the subset: a construct it cannot
translate fails closed with a message naming it, reported as `OAK-K0101` on
the kernel. Two rules the emitter cannot judge alone are checked beside it:

- **Loops are canonical** (`85-discipline.md` section 3) in every function
  a kernel reaches, in every profile — `OAK-K0102` names the kernel and the
  loop. A GPU thread with an unbounded loop hangs the device.
- **A kernel has no effects** — `OAK-K0103`. Its closure over declared
  clauses, effect rows (`60-effects-allocation.md` section 2a), and callees
  is empty and fully known: an undeclared extern or an unrowed function
  value in reach rejects.

Inside the subset:

| Oak | Metal Shading Language |
| --- | --- |
| `u8 u16 u32 u64` / `i8 i16 i32 i64` / `f32` / `Bool` | `uchar ushort uint ulong` / `char short int long` / `float` / `bool` |
| `[]T` parameter | `device const T* x [[buffer(n)]], constant uint& x_len [[buffer(n+1)]]` |
| `[*]T` parameter | `device T* y [[buffer(n)]], constant uint& y_len [[buffer(n+1)]]` |
| scalar parameter | `constant T& s [[buffer(n)]]` |
| the grid position | `uint gid [[thread_position_in_grid]]` |
| locals `x: T = e`, `x := e`, assignment | the same, scalars only |
| `x[i]`, `y[i] = v` | `x[oak_check(i, x_len, oak_fault)]` — the index is checked against the length and a miss raises the fault word (section 3) |
| `len(x)` | `x_len` |
| `+ - *` on integers | wrapping in the operand's width: plain for `u32`/`u64`; narrow and signed types compute in the unsigned carrier and cast back, so no signed overflow is ever evaluated |
| `/ %` on integers | `oak_div_T` / `oak_rem_T`: a zero divisor raises the fault; `MIN / -1` gives `MIN` and remainder `0` (`20-types.md` section 11.1) |
| `<< >>` | `oak_shl_T` / `oak_shr_T`: a count reaching the width raises the fault |
| `& \| ^`, prefix `^`, prefix `-` | the operators, cast to the operand's width; negation is two's complement |
| `+ - * /` on `f32`, comparisons, `&& \|\| !` | the operators |
| `T(x)` widening and float constructors; `T_trunc_S`, same-width `T_bits_S` between integers, `f32_bits_u32`/`u32_bits_f32`, `f32_round_S` from an integer | casts, `as_type<T>` for float bits |
| `fma sqrt abs copysign floor ceil trunc round round_even min max min_num max_num is_nan is_finite is_infinite is_normal` | `fma`, `precise::sqrt`, `fabs`, `copysign`, `floor`, `ceil`, `trunc`, `round`, `rint`, `oak_fmin`/`oak_fmax` (NaN-propagating, IEEE 754-2019 `minimum`/`maximum`), `fmin`/`fmax`, `isnan`, `isfinite`, `isinf`, `isnormal` |
| `cond ? a \| b` | `if`/`else` in statement position (an empty else is dropped), `cond ? a : b` in value position with expression arms |
| `while cond { }`, `break` | the same |
| a call to a helper | a call to the emitted `static inline` function, buffers passed as pointer and length, the fault word last |

Outside the subset in this increment, each failing closed by name:
`f64`, `f16`/`bf16`, records and their fields, fixed arrays as
parameters or locals, ADTs and variant matches, strings, `subslice`,
`view`/`span` of a local, `assert`, `total_order`, the saturating,
checked, and trapping conversion rows, integer-constant matches, block
arms in value position, calls through function values, globals and
constants, generics (call an instantiation), methods, recursion.

## 3. Traps and the fault word

Oak traps on an index past the end, a zero divisor, and a shift count
reaching the width. A GPU thread cannot trap. Every emitted kernel takes one
more buffer, the **fault word** (`device atomic_uint* oak_fault`, the last
buffer index in the descriptor): a trapping condition stores a nonzero code
into it (1 index, 2 divisor, 3 shift) and yields zero to the expression, and
the thread continues with unspecified results. **The host checks the fault
word after the command buffer completes; a nonzero value is the trap.** The
outputs of a faulted launch are unspecified, exactly as the state after an
Oak trap is unreachable; a host that reads them anyway has left the
language. The C realization traps at the same conditions, on the thread
that meets them.

Every buffer access is checked in this increment. Eliding a check the
checker has discharged — a `while i < n` bound with `n = len(x)` proves
`x[i]` in range — is the recorded next step; the emitted form makes the
cost visible, one compare per access, which is the fight for performance
this design asks the author to win with a proof rather than a flag.

## 4. Floating point

Oak floating point is one rounding per operation, no contraction, no
reassociation (`20-types.md` section 11.3). Metal compiles with fast math
by default, which breaks all three. The emitted file pins
`#pragma METAL fp math_mode(safe)` and `#pragma METAL fp contract(off)`,
and its header tells the host to compile with
`MTLCompileOptions.mathMode = MTLMathModeSafe` (`fastMathEnabled = NO` on
older SDKs). A host that compiles the file with fast math has changed the
kernel's meaning; the descriptor states the requirement, the compiler cannot
enforce it. `sqrt` is emitted as `precise::sqrt` so it is correctly rounded;
`fma` is one rounding as in Oak.

## 5. Launch descriptors

The emitted file begins with one line per kernel, machine-readable:

```text
// oak-kernel relu: gid grid; x view f32 buffer 0,1; y span f32 buffer 2,3; fault buffer 4
// oak-kernel axpy: gid grid; a scalar f32 buffer 0; x view f32 buffer 1,2; y span f32 buffer 3,4; tile scalar u32 buffer 5; fault buffer 6
```

Fields are `;`-separated: the kernel name, then each parameter as
`name kind element buffer indices` (kind `grid`, `view`, `span`, or
`scalar`; a view or span occupies two indices, data then length; a scalar
one), then the fault buffer. The same information is `compiler.
Compilation.EmitMetal()`'s `Result.Kernels` for tools in Go. The host binds
each view or span as a buffer of `element` values plus a `uint` length —
`c.span_of`/`c.mut_span_of` (`92-ffi.md` section 2.5) are the Oak side of
that boundary — scalars as single-value buffers, and a zeroed `uint` for
the fault word; dispatches `grid` threads; checks the fault word.

## 6. Order independence (Lean)

A launch runs the body once per grid position; the C realization runs the
positions in order and a GPU in any order. They agree when the threads are
**independent**: each position's writes are disjoint from every other
position's reads and writes — the condition `55-parallelism.md` section 2
requires of a parallel iteration space. `Oak.Kernel`
(`spec/lean/Oak/Kernel.lean`) models a thread as a framed step on memory
(it changes only its write footprint and depends only on its read
footprint) and proves `commute` (independent threads commute) and
`run_perm`: running independent threads in any order gives the same
memory, so the sequential C loop and the GPU launch compute one result.

The independence obligation is the kernel author's in this increment: the
checker does not yet prove that `y[gid]` and `y[gid']` are disjoint for
`gid ≠ gid'`. The two shapes the pilot uses — one element per thread, and a
tile of `tile` elements per thread starting at `gid * tile` — satisfy it
by construction; a checker rule that recognizes them is the recorded next
step, with unknown independence failing closed as section 2 of the
parallelism chapter requires.

## 7. What this increment does not do

- Execute on a GPU from `oak run` or `oak test`: the host side (device,
  pipeline state, command buffer) is the runtime's, reached through
  `c.extern` and `framework Metal` in `oak.mod`. The Metal toolchain is not
  part of the compiler's tests; the emitted text is checked against its
  stated form and the C realization is executed.
- Threadgroup memory, SIMD-group operations, barriers, atomics beyond the
  fault word, or reductions across threads. `reduce.tree` (`55-parallelism.md`
  section 4) inside a kernel body is a helper call like any other and runs
  per thread; a cross-thread reduction with the same fixed grouping is the
  planned second increment.
- Records and fixed arrays as kernel parameters (F6's tensors are records
  over views; the kernel takes the views).

## 8. Tensors over views (`import("tensor")`)

**Status: implemented (library), 2026-09-12.** The ml pilot's request F6:
tensors as typed records over shapes and views. The library is
`stdlib/tensor.oak`; what it needed from the language already existed —
region records over views and spans (`50-borrowing.md` §8b, §8c), generic
region parameters, `assert` — so no compiler change was made for it, and
the record is host-side structure over the buffers a kernel takes.

```oak
t := import("tensor")

a: t.Tensor2 = t.tensor_of(view(&xs), 2, 3)        // shape over a view, row-major
at: t.Tensor2 = t.tensor_transpose(a)               // strides swapped, same storage
{
  o: t.MutTensor2 = t.tensor_mut_of(span(&ys), 2, 2) // results into a caller-owned span
  t.tensor_matmul(a, at, o)
}
```

- `Tensor2[R]` is `{ data: View[f32, R], rows, cols, row_stride, col_stride,
  offset }`; `MutTensor2[R]` the same over `Span[f32, R]`. Element `(i, j)`
  is `data[offset + i * row_stride + j * col_stride]` after the shape check
  (`tensor_index` traps on an out-of-shape pair; the view's bounds check
  guards the storage). `tensor_transpose` swaps the strides and
  `tensor_row` moves the offset: new records, no copies.
- **Nothing allocates.** `tensor_matmul`, `tensor_relu`, `tensor_add`,
  `tensor_scale`, and `tensor_fill` write into a `MutTensor2` the caller
  built over storage it owns — a fixed array, a `Buffer` in host custody
  (§2.8.5 of `92-ffi.md`), an arena reservation. The borrow rules apply
  unchanged: while the mutable tensor is live its owner is suspended, so
  the result is read after the tensor's block ends.
- **Reductions name their grouping**: `tensor_sum` and the inner product
  of `tensor_matmul` are the sequential left fold in row-major order, the
  grouping every backend computes; a tree-grouped variant is `reduce.tree`
  (`55-parallelism.md` §4) over the same elements.
- **Kernels take the tensor's parts.** A kernel takes `t.data` as a view
  or span and the shape scalars as `u32` parameters (§1); the per-element
  body is the library function's inner statement. Records as kernel
  parameters are the increment that would let a kernel take the tensor
  itself.

`Oak.Stdlib.TensorLaws` (`spec/lean/Oak/Stdlib/TensorLaws.lean`) proves
over the extraction (`TensorExtracted.lean`, regenerated from the Oak
source) that reading the transpose at `(i, j)` is reading the original at
`(j, i)`, shape check included (`at_transpose`), that transposing twice is
the identity (`transpose_transpose`), and that a row reads as the original
(`at_row`). Specifications of `tensor_matmul` and `tensor_sum` against a
mathematical definition are the recorded next step, with the checker rule
for kernel-thread independence over `tensor_index`.

