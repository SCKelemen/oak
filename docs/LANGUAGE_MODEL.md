# Oak Language Model

Oak is a systems language in which one checked semantic definition should drive every projection that can soundly reuse it.

> Define a fact once; project it many ways.

The language is organized around five orthogonal semantic axes.

## 1. Type: what does this value mean?

Types carry semantic identity independent of representation.

Examples:

```oak
UserId: type = Id[User]
OrderId: type = Id[Order]
PhysAddr: type = Address[Physical]
VirtAddr: type = Address[Virtual]
```

Two types may have identical bits and still be different values to the type checker, proof system, debugger, and schema tools.

The type axis includes:

- scalar and nominal identity;
- records/products;
- sums/ADTs;
- functions;
- generic parameters and constraints;
- phantom parameters;
- aliases and opaque types.

Algebraic data types and pattern matching remain the center of ordinary Oak programming.

## 2. Representation: what bits represent it?

Representation is separate from type meaning.

A semantic type may specify or derive:

```text
bit width
size
alignment
field offsets
tag/discriminant layout
endianness
calling/ABI representation
```

Machine integers (`u8`, `u16`, ..., `int`, `uint`, `iptr`, `uptr`) are not silently identified with mathematical integers.

A type with no explicit representation constraint leaves representation to the executable backend. A wire/MMIO/ABI type may constrain it exactly.

### ADT payloads, discriminants, and defaults are distinct

These concepts must not share ambiguous syntax or semantics:

- a variant payload;
- a machine discriminant/value;
- a default field value;
- arbitrary metadata.

Conceptually:

```oak
Result[T, E]: type =
  | Ok(T)
  | Err(E)

Status: type @repr(u16) =
  | Ok       @value(200)
  | NotFound @value(404)

Config: type =
  retries: u8 = 3
```

Exact surface syntax remains open, but the Semantic IR must distinguish these facts now.

### Record composition, not accidental structural subtyping

Oak's existing `A & B` record-definition feature is representation/type composition. The resulting type remains nominal unless structural subtyping is explicitly designed later.

Constraint conjunction such as `T: Reader & Writer` means that `T` satisfies both constraints. These are separate semantic operations even if surface syntax eventually shares `&`.

## 3. Authority and effects: what may code holding it do?

Ownership, borrowing, capabilities, effects, and unsafe boundaries belong to one authority axis.

Existing Oak concepts:

```text
[N]T    owned fixed storage
[]T     shared read-only view
[*]T    unique writable span
*T      raw pointer
```

should evolve into explicit semantic states rather than merely syntax conventions.

Examples:

```text
CpuOwned[Buffer]
DeviceOwned[Buffer]
SharedRead[Buffer]
UniqueWrite[Buffer]
```

A DMA transfer can therefore be one checked state transition:

```text
CpuOwned[Buffer] -> DeviceOwned[Buffer] -> CpuOwned[Buffer]
```

Effects are also authority facts:

```oak
realtime fn process(...)
  effects { Audio.Read, Audio.Write }
  forbids { Memory.Allocate, Thread.Block, Os.Syscall }
```

A required effect and a forbidden effect may not be the same semantic effect.

### `unsafe` is a boundary, not an off switch

`unsafe` means Oak cannot establish one or more normal safety invariants for the operation. It does not disable type checking, layout checking, effect checking, or unrelated proofs.

Unsafe primitives should eventually state the assumptions they introduce so that higher-level code can contain and discharge those assumptions explicitly.

## 4. Proposition: what facts are known?

Refinements, preconditions, postconditions, invariants, and derived facts are structured propositions.

Conceptually:

```oak
IrqId[N]: type = u16 where value < N
AlignedPage: type = uptr where value % PageSize == 0
```

The compiler should preserve proposition structure rather than converting it to an opaque annotation string. The same proposition can then drive:

- ordinary static checking;
- bounds-check elimination;
- SMT obligations;
- Lean definitions/theorems;
- generated boundary/property tests;
- documentation.

Proof status is explicit:

```text
specified
checked
proved-smt
proved-kernel
model-checked
tested
refined
```

Oak must never collapse these statuses into a vague `verified` bit.

## 5. Protocol: how may state evolve over time?

A function describes one computation. Systems code also needs to describe legal state evolution and concurrent behavior.

Conceptually:

```oak
protocol VirtualIrq
  state Idle
  state Pending
  state Active

  transition inject Idle -> Pending
  transition acknowledge Pending -> Active
  transition eoi Active -> Idle
```

One protocol definition should eventually drive:

- local typestate APIs;
- executable state-machine scaffolding;
- temporal/model-checker projection;
- Lean transition definitions;
- deterministic simulator actions;
- state diagrams;
- debugger state decoding.

Liveness properties must state environmental assumptions such as scheduler fairness, device progress, or peer behavior.

## One semantic definition, many projections

```text
                         +-> executable code / C / native
                         +-> machine layout / ABI
                         +-> serialization / wire schema
Oak source -> Semantic IR +-> debugger metadata
                         +-> SMT
                         +-> Lean
                         +-> temporal model checker
                         +-> property tests / DST
                         +-> documentation / UI schema
```

The Semantic IR, not any one backend, is the semantic source of truth.

## Existing features in this model

Oak already has useful precursors for all five axes:

| Existing feature | Semantic role |
| --- | --- |
| ADTs / records / generics | Type |
| fixed-width integers / pointers / C layout | Representation |
| views / spans / borrow checking / `unsafe` | Authority |
| phantom types / constraints | Type + Proposition |
| struct tags | Extensible projection metadata |
| pattern matching / ADT transitions in code | Seed for Protocol |

Struct tags remain useful, but correctness-critical concepts graduate from arbitrary metadata into typed semantic constructs.

## String validity

Encoding is a semantic property, not just a phantom label on arbitrary bytes.

Conceptually:

```text
Bytes
ValidatedBytes[Utf8]
Str[Utf8]
```

Converting arbitrary bytes to `Str[E]` must validate the encoding or require an explicit unsafe assumption. A safe `from_bytes` cannot simply assert that arbitrary bytes are valid UTF-8/UTF-16/etc.

## Interfaces and dynamic dispatch

Interface constraints are compile-time capabilities by default:

```oak
fn copy[R: Readable, W: Writable](r: R, w: W): ()
```

should not imply a hidden vtable or heap allocation.

If Oak later supports runtime existential/interface values, that dynamic representation must be explicit in the type and representation axes.

## C is a backend, not the definition of Oak

Readable C remains a valuable bootstrap backend and audit surface. Oak's language semantics must not be defined as "whatever the C backend happens to do."

The long-term pipeline is:

```text
Oak source
  -> syntax tree
  -> semantic analysis
  -> Semantic IR
      -> C
      -> native lowering
      -> Lean
      -> temporal model
      -> schemas/tooling
```

## Syntax remains orthogonal

Oak has one language grammar with two equivalent block spellings:

- layout/indentation style;
- explicit brace style.

Both normalize before semantic analysis. None of the five semantic axes may depend on which style the programmer used.

## Implementation rule

The Semantic IR should fail closed when the compiler has lost information.

For example, the current syntax AST historically stores record fields in a Go map. A backend may not invent a deterministic machine field order from that map and claim it is source layout. Exact representation facts become available only after the syntax/typed AST preserves the ordering needed to justify them.

This principle applies generally:

> Missing semantic information remains unknown; it is never reconstructed by guesswork.
