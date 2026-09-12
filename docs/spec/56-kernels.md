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
  (read and write) of a scalar `T` — **scalars**, or **records** of those
  (a `Tensor2[R]`: its view and its shape scalars; `kernel relu[R, S]:
  (gid: u32, x: Tensor2[R], out: MutTensor2[S])` with the region
  parameters a record over borrows needs). Scalars are `u8` through `u64`,
  `i8` through `i64`, `f32`, and `Bool`. `f64` is outside the subset
  (Apple GPUs have no double precision); records inside records, fixed
  arrays as parameters, strings, and ADTs are outside.
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
| record parameter `t: Tensor2[R]` | its fields **flattened** into consecutive buffers in declaration order (`t.data view f32 buffer 0,1; t.rows scalar u32 buffer 2; …` in the descriptor) and rebuilt as a struct local, `tensor__Tensor2 t = { t__data, t__data_len, t__rows, … };`, for the body |
| a record in a helper: parameter, result, local, literal | the MSL `struct` of the record (a buffer field is a pointer and its length), passed and returned by value; `Tensor2 { data: v, rows: r, … }` is `tensor__Tensor2{ v, v_len, r, … }` |
| `t.rows`, `t.data[i]`, `len(t.data)`, `t.data[i] = v` | the struct field; a buffer field is indexed, measured, windowed, or passed on like a buffer parameter |
| `assert(cond)` | `if (!cond) { oak_raise(oak_fault, 5u); return zero; }` — a failed assertion is a trap (section 3), and the thread leaves the function with a zero result |
| `r.group_tree(G, xs, lo, m, zero, f)` in a kernel body | the **cooperative reduction** of section 7: the kernel becomes a group kernel with `G` threads per position; `G` is an integer literal, a power of two up to 1024, one per kernel |
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
| a helper with function-valued parameters, called with named functions (`r.tree(part, zero, add)`) | the helper is emitted once **per binding** — `reduce__tree_f32__add` — with calls through the parameter replaced by calls to the bound function; the argument must name a function of the program (no function pointers reach the GPU) |
| `w: []T = subslice(buf, start, n)`, `v: []T = buf` | a **window**: `device const T* w = buf + oak_subslice(start, n, buf_len, fault); uint w_len = n;` — `start + n <= len` is checked in 64-bit and a miss raises fault 4; a bare name aliases the buffer whole; a span window needs a span source |
| `a: [N]T = [ ... ]`, `a: [N]T` | a thread-private fixed array, `T a[N] = { ... };` (zeroed when uninitialized), indexed with the check against `N` unless proven |
| `cond ? a \| { stmts; v }` in result position | `if`/`else` whose arms return, the block's statements emitted in place |

Outside the subset, each failing closed by name: `f64`, `f16`/`bf16`,
records inside records, fixed arrays as parameters, ADTs and variant
matches, strings, `subslice` outside a window declaration, `view`/`span`
of a local, `total_order`, the saturating, checked, and trapping
conversion rows, integer-constant matches, block arms in value position
other than a result, calls through function values that are not bound to
a named function, globals and constants, generics (call an
instantiation), methods, recursion.

## 3. Traps and the fault word

Oak traps on an index past the end, a zero divisor, and a shift count
reaching the width. A GPU thread cannot trap. Every emitted kernel takes one
more buffer, the **fault word** (`device atomic_uint* oak_fault`, the last
buffer index in the descriptor): a trapping condition stores a nonzero code
into it (1 index, 2 divisor, 3 shift, 4 window past the end, 5 assertion) and yields zero to the expression, and
the thread continues with unspecified results. **The host checks the fault
word after the command buffer completes; a nonzero value is the trap.** The
outputs of a faulted launch are unspecified, exactly as the state after an
Oak trap is unreachable; a host that reads them anyway has left the
language. The C realization traps at the same conditions, on the thread
that meets them.

A buffer access the checker has **discharged** (`50-borrowing.md` §8,
`typechecker/extents.go`, laws in `Oak.Extents`) is emitted as the raw
load or store; every other access goes through the check. The forms a
kernel meets: a guard `gid < len(y) ? { y[gid] = ... }` proves the store
for the arm; `len(x) == len(y)` in the same guard transfers the bound to
`x[gid]`; the canonical strict loop `n: u32 = len(x)` … `while i < n {
x[i] }` proves every access in the body (the binding of `len(x)` is an
upper bound for indices into `x`, `bound_through_upper`). The emitted form
keeps the cost visible — a compare per access the author has not
discharged — which is the fight for performance this design asks the
author to win with a proof rather than a flag.

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
`name kind element buffer indices` (kind `grid` or `group` for the
position, `view`, `span`, or `scalar`; a view or span occupies two indices,
data then length; a scalar one; a record parameter is its fields as
`name.field`), then the fault buffer, the independence shape, and for a
group kernel `threadgroup G`: the host dispatches `positions * G` threads
in threadgroups of `G`, and each position is one threadgroup. The same information is `compiler.
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

**The checker discharges independence** for the two shapes a kernel
author writes, and rejects every other span access (`OAK-K0104`, naming the
access), as section 2 of the parallelism chapter requires of unknown
independence:

- **one element per thread**: every span access is at the grid position,
  `y[gid]`;
- **a tile per thread**: every span access is at `gid * T + k` — spelled
  directly, through a local `base: u32 = gid * T`, or through a local
  `i: u32 = base + k` — where `k` is the counter of an enclosing
  `while k < T` whose body changes `k` only as its last statement, and `T`
  is a scalar parameter or a literal; none of `gid`, `base`, `i`, or `T`
  is reassigned.

Views are read-only and impose nothing; a span — or a record holding one
— handed to a helper, windowed, or rebuilt in a literal takes its accesses
out of the kernel's sight and is rejected (index the span, or the span
field, in the kernel body). A span field `out.data` is judged as the span
`out.data`. `Oak.Kernel.element_disjoint` and `tile_disjoint` prove
the two footprints pairwise disjoint for distinct positions, which is
`Independent` for the spans, so `run_perm` applies. The tile fact is over
the natural numbers: the descriptor records the shape (`independence:
tile T`) and the host's obligation is that `grid * T` fits the `u32`
index, which any buffer the tiles cover already guarantees.

## 7. What this increment does not do

- Execute on a GPU from `oak run` or `oak test`: the host side (device,
  pipeline state, command buffer) is the runtime's, reached through
  `c.extern` and `framework Metal` in `oak.mod`. The Metal toolchain is not
  part of the compiler's tests; the emitted text is checked against its
  stated form and the C realization is executed.
- SIMD-group operations, atomics beyond the fault word, and threadgroup
  memory other than the cooperative reduction's scratch. Reductions are
  in, two ways. **Within a thread**: `reduce.tree` over a window of the
  input, its combine bound to a named function, runs per thread with the
  binary-counter grouping the host computes. **Across a threadgroup**:
  `r.group_tree(G, x, lo, m, zero, add)` in a kernel body makes the kernel
  a **group kernel** — its position is a threadgroup of `G` threads
  (`[[threadgroup_position_in_grid]]`; `G` a literal power of two up to
  1024, one per kernel, `threadgroup G` in the descriptor). The threads
  load the `m` elements at `lo` into threadgroup scratch (`m <= G` and
  the window fitting are checked, faults 5 and 4) and combine
  **pairwise-adjacent with doubling stride**, partner present, behind
  barriers; every thread reads the result, and one thread performs the
  kernel's span stores. On the host `group_tree` is `tree` over the
  window; `Oak.Reduce.coop_eq_tree` proves the cooperative scheme
  computes the same binary-counter tree for every `m`, so `partials[gid]`
  is the same bits on the GPU and the CPU, and a launch's total —
  `reduce.tree` over the partials on the host — is "tree of group trees",
  a language fact. Every Oak value in a group kernel depends only on the
  position and the parameters, so the barriers are reached uniformly by
  construction.
- Fixed arrays as kernel parameters (a fixed array is thread-private; a
  buffer is a view or span).

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
- **Kernels take tensors.** `kernel relu[R, S]: (gid: u32, x: Tensor2[R],
  out: MutTensor2[S])` takes the records themselves (§1): the Metal entry
  flattens each into its buffers and rebuilds the struct, `tensor_at(x, i,
  j)` runs as a helper taking the record by value, and `out.data[gid]` is
  the store the independence rule judges. A helper that writes through a
  record's span (`tensor_set(out, …)`) is rejected inside a kernel because
  its indices leave the kernel's sight. **The idiom for a tensor-shaped
  output** is one element per position, stored flat under a contiguity
  guard:

  ```oak
  kernel matmul[A, B, C]: (gid: u32, a: Tensor2[A], b: Tensor2[B], out: MutTensor2[C]): () = {
    contiguous: Bool = out.row_stride == out.cols && out.col_stride == 1 && out.offset == 0
    contiguous && gid < out.rows * out.cols && gid < len(out.data) && a.cols == b.rows ? {
      i: u32 = gid / out.cols
      j: u32 = gid % out.cols
      acc: f32 = 0.0
      k: u32 = 0
      n: u32 = a.cols
      while k < n {
        acc = acc + tensor_at(a, i, k) * tensor_at(b, k, j)
        k = k + 1
      }
      out.data[gid] = acc
    }
  }
  ```

  `Oak.Stdlib.Tensor.flat_index` proves, over the extraction, that in a
  contiguous tensor `tensor_index` places `(gid / cols, gid % cols)` at
  `gid` for every `gid` below `rows * cols`, so the flat store writes the
  element `tensor_set` would; the guard makes the kernel's store the
  element shape and its loads go through the shape-checked helper. The
  inner product is the sequential left fold of `tensor_matmul`, so the
  kernel and the library compute the same bits.

`Oak.Stdlib.TensorLaws` (`spec/lean/Oak/Stdlib/TensorLaws.lean`) proves
over the extraction (`TensorExtracted.lean`, regenerated from the Oak
source) that reading the transpose at `(i, j)` is reading the original at
`(j, i)`, shape check included (`at_transpose`), that transposing twice is
the identity (`transpose_transpose`), and that a row reads as the original
(`at_row`). Specifications of `tensor_matmul` and `tensor_sum` against a
mathematical definition are the recorded next step, with the checker rule
for kernel-thread independence over `tensor_index`.

