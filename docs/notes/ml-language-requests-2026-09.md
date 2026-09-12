# Note: the ml pilot's language requests F1–F6, assessment and plan

**Status: in progress, 2026-09-12.** Baseline: `specification` at `ed56b3e`; round one (F2 + F3) landed as #207, round two (F4) as #213; round three (F1, first increment) as #217; round four (F5) follows.
Source: the ml tensor-compiler pilot's second request list, relayed after
its kernels moved from emitted strings toward code. The pilot's stated goal
is the design principle this note adopts: **find the optimal structure for
the golden use case, wrap it in correctness proofs, and make that the
simplest thing a user can write** — the language dictates the fast
implementation; the user never fights for performance.

| # | Request | What exists | Disposition |
| --- | --- | --- | --- |
| F1 | Kernels as Oak functions in the strict subset, compiled to Metal and C, so emitters become code a proof can name | The C backend, the strict profile (bounded loops, no allocation), Lean extraction of Oak functions (`95-extraction.md`), asm units beside sources (`94-assembler.md`), spans across the FFI | **Round three — landed, first increment** (`56-kernels.md`). `kernel name: (gid: u32, ...): () = ...` declares a function in the kernel subset; the C backend compiles it as an ordinary function (the host loop is the launch), `oak build -metal` emits a Metal compute kernel with `[[buffer(n)]]` bindings and a launch descriptor line per kernel, and the Lean extraction states it. Traps become a fault word the host checks; integer wrapping and safe float math are preserved. The compiler holds kernels to the subset in every build (`OAK-K0101`–`K0103`). `Oak.Kernel` proves independent threads run in any order give one result. Not yet: check elision from discharged bounds, threadgroup memory and cross-thread reductions with `reduce.tree`'s grouping, records as parameters, a checker rule for thread independence. |
| F2 | A reduction primitive whose lane order is a language fact | `simd.reduce_add` is a specified pairwise tree (`93-simd.md` §1.2a, `55-parallelism.md` §4, fourth option) | **Round one — landed.** `reduce.tree[T](xs, zero, f)` (`stdlib/reduce.oak`) over a view with the **balanced binary-counter tree** as its semantics — a stack of partials with levels, equal-level neighbours combine, leftovers combine right to left — so four lanes give `(x0 + x1) + (x2 + x3)`, exactly `reduce_add`, and any count gives one fixed tree; empty is `zero`; `reduce.left` is the sequential fold. Written in the strict subset, so the same code runs in C and the interpreter; `Oak.Reduce` (Lean) defines the same tree and proves the concrete groupings and `tree_assoc`. The binary-counter tree replaced the note's midpoint recursion because it is a single bounded loop with a 64-entry stack — the shape the strict profile admits and a kernel can carry. |
| F3 | Declared operator properties as the permission to reorder | Operator definitions (`10-syntax.md` §14) bind `+` to one named function; ml's fast-matmul flag reorders on the author's say-so | **Round one — landed.** `laws { associative, commutative }` on an operator definition (`10-syntax.md` §14a), validated against the signature and recorded by the checker (`OperatorLaws`, `HasOperatorLaw`); the only permission a backend has to regroup. `oak vet` lists declared laws beside the recorded assumptions; the REPL's `:lean` extracts the operator function and states each law as a theorem over it (`law_add_associative`, elaborates with `sorry`). Not yet consumed by a backend — F1's kernel lowering is the first consumer. |
| F4 | Effect-typed steps, so a host read inside a step is a compile error | `effects`/`forbids` clauses checked over the concrete call graph (`60-effects-allocation.md` §2); a call through a function value has unknown effects and fails a `forbids` (`OAK-E0103`) | **Round two — landed.** Effect rows on **function types** (`60-effects-allocation.md` §2a): `step: ([]u8) -> () effects { }` is a type; a call through a rowed value contributes the row, so a `forbids` sees through it; every value entering a rowed type is checked against the row after specialization (`OAK-E0105`), unknown effects failing closed. `Host.Read`/`Device.*` are ordinary `Namespace.Name` classes the runtime's externs declare. `Oak.EffectRows` proves the check sound (`perform_subset_bound`, `forbids_sound`). Not checked: flows other than arguments and declaration initializers (assignment, fields, returns). |
| F5 | Custody typestates on buffers | Typestate-indexed resources (`112-protocols.md` §5a) with `via` transitions and consumption; `Buffer[T]` owning runtime memory (`92-ffi.md` §2.8); the `Buffer[CpuOwned] → Buffer[DeviceOwned]` design (`50-borrowing.md` §11) | **Round four — landed** (`92-ffi.md` §2.8.5). `Buffer[T, S]` with `Host` initial; a custody transition is an extern binding `(b: Buffer[T, Host]): Buffer[T, Device]` — the runtime's function gets pointer and count, the Oak result is the same buffer re-typed, the old binding is consumed; `view`/`span`/`c.disown` only at `Host`. Chosen over `via` callables because the transition's side effect (enqueue, fence) is the runtime's, so the extern binding is the natural trust boundary. `Oak.BufferCustody` instantiates `Oak.Typestate`. Not yet: a buffer inside a record, states carrying a device identity. |
| F6 | Tensors as typed records over shapes and views | Const parameters and generic records (`Ring[T, N]`), views and spans, operator definitions, uniform call syntax | **Round five, library-first.** `Tensor[T, R]` as a record of a shape `[R]u32`, strides, and a view; `matmul`, `relu`, and reductions written over it with `operator` bindings and F2's `reduce`; strict-subset kernels (F1) are the bodies. What needs the compiler — shape arithmetic on const parameters — is decided by writing the library first. |

## Order and why

1. **F2 + F3** — small, foundational, and they fix the semantics every
   later round leans on: what a reduction means, and when it may be
   regrouped. They also exercise the proof path end to end (a declared law
   becomes a Lean theorem over the extracted function).
2. **F4** — a contained checker extension with an exact pilot ask behind
   it.
3. **F1** — the Metal emitter, once kernel bodies have fixed reduction
   semantics and effect-typed steps to launch them.
4. **F5** — buffer custody on the typestate machinery.
5. **F6** — the tensor library, informed by what F1 kernels need.

## The regex question

The pilot also asked whether the simdjson, tinygrad, and mlx techniques
give the most performant regex engine. For Oak the relevant pieces are
already the language's: byte classification with `simd.U8x16` compares and
masks (`93-simd.md`), table-driven state machines with proven accesses
(the UTF-8 and codec work in `stdlib/strings.oak`), and the strict profile
for the matching loop. A regex engine as a golden use case would be a
stdlib workstream after this list: a DFA compiler in Oak, SIMD prefilters
for literal fragments (the simdjson technique), and extraction of the DFA
step for proofs of match semantics. It is recorded here, not started.
