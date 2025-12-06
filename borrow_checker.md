# Borrow Check Spec

Formal specification of Oak's borrowing model for arrays, spans, and views, including slice notation.

---

## 1. Goals

The borrowing system in Oak is intentionally small and MCU-friendly. It aims to:

* Provide **basic aliasing guarantees** for contiguous memory (arrays and slices).
* Compile down to **simple C structs and pointers** (no runtime metadata, no refcounts).
* Work naturally with Oak's **views** (`[]T`) and **spans** (`[*]T`).
* Support **Go-like slice notation**, extended with **Python-style negative indices**.
* Stay far away from Rust/Scala-level complexity (no lifetimes in the surface language, no monad towers).

The borrow checker is a **static analysis** pass; it does not change generated C layouts.

---

## 2. Ownership & Borrowing Types

Oak has three core container shapes for contiguous memory:

```oak
// Owned, fixed-size buffer
[N]T

// Read-only, non-owning window
[]T

// Read/write, non-owning window
[*]T
```

### 2.1. Desugared definitions

At the type level, these are sugar for two generic record types:

```oak
Byte: type = u8

View[T]: type =
  { base: *T
  , len:  u32
  }

Span[T]: type =
  { base: *T
  , len:  u32
  }

// Sugar
[]T  == View[T]
[*]T == Span[T]
```

For now, `View` and `Span` are contiguous ranges with stride +1.

### 2.2. Runtime representation (C backend)

The C backend always generates the same simple layouts:

```c
typedef struct {
  T*  base;
  u32 len;
} oak_view_T;

typedef struct {
  T*  base;
  u32 len;
} oak_span_T;
```

The borrow checker does not add fields or change these layouts.

---

## 3. Borrow States

For each **owned array variable** `x` of type `[N]T`, the borrow checker tracks a small abstract state:

```text
BorrowState(x) ::=
  Free               // no active borrows
  SharedRead         // ≥ 1 read-only borrows (View/[]T)
  UniqueWrite        // exactly 1 writable borrow (Span/[*]T)
```

The checker only tracks ownership/borrows for:

* owned arrays `[N]T`
* views `[]T` / `View[T]`
* spans `[*]T` / `Span[T]`

Raw pointers (`*T`) and `unsafe` code are **not** tracked.

---

## 4. Lexical Borrowing Rules (v1)

### 4.1. High-level rules

**Rule 1 — Many readers OR one writer (per owner)**

For a given owned array `x: [N]T` at any program point:

* Either: `BorrowState(x) == Free`.
* Or: `BorrowState(x) == SharedRead` and there may be one or more `View` / `[]T` borrows pointing into `x`.
* Or: `BorrowState(x) == UniqueWrite` and there is exactly one `Span` / `[*]T` borrow pointing into `x`.
* But never both SharedRead and UniqueWrite at the same time.

**Rule 2 — Borrows are lexical (v1)**

* A borrow (view or span) is considered *live* from its declaration until the end of the enclosing block.
* Borrows **cannot escape** the block in which they are created (v1 restriction):

  * they may not be stored into longer-lived structs,
  * they may not be returned from the function,
  * they may not be assigned to variables declared outside the block.

At block end, all borrows created in that block are dropped, and the owner state may return to `Free`.

**Rule 3 — Spans are unique writers**

* A `Span[T]` / `[*]T` is a unique mutable borrow of its owner.
* While a `Span` into `x` is live, no new views or spans may be created into `x`.

### 4.2. Borrow creation primitives

Conceptually, the borrow checker treats these operations as the primitive sources of borrows:

```oak
// From owned array to view/span
fn (arr: *[N]T) view() -> []T
fn (arr: *[N]T) span() -> [*]T

// Sub-slicing of existing view/span
fn subslice[T](v: View[T], start: u32, len: u32) -> View[T]
fn subslice[T](s: Span[T], start: u32, len: u32) -> Span[T]
```

These may be surface-level methods or just desugaring targets; the spec describes their *effect on borrow state*.

#### 4.2.1. Creating a view from an owner

```oak
v: []byte = buf.view()
```

* Precondition: `BorrowState(buf) ∈ { Free, SharedRead }`.
* Postcondition: `BorrowState(buf) = SharedRead`.
* The checker records `OwnerOf(v) = buf`.

#### 4.2.2. Creating a span from an owner

```oak
s: [*]byte = buf.span()
```

* Precondition: `BorrowState(buf) == Free`.
* Postcondition: `BorrowState(buf) = UniqueWrite`.
* The checker records `OwnerOf(s) = buf`.

#### 4.2.3. Sub-slices of views/spans

```oak
v2 := subslice(v, start, len)
```

* `v2` shares the same owner as `v` (i.e., `OwnerOf(v2) = OwnerOf(v)`).
* No change to `BorrowState`.
* `v2` is not an independent borrow; it is a derived handle within the same borrow.

Same for spans:

```oak
s2 := subslice(s, start, len)
```

* `OwnerOf(s2) = OwnerOf(s)`.
* No change to `BorrowState`.

### 4.3. End-of-block semantics

At the end of a block `{ ... }`, all locals declared inside that block go out of scope.

The checker:

* Removes any `View`/`Span` variables from `OwnerOf`.
* For each array owner `x: [N]T`, recomputes:

  * If no active borrows into `x` remain in scope, set `BorrowState(x) = Free`.

Because v1 forbids borrows from escaping their creation block, this recomputation is straightforward.

### 4.4. Errors detected

The borrow checker must reject patterns such as:

```oak
fn bad() -> () {
  buf: [16]byte = zero_init()

  // 1. Span while view is live.
  {
    v: []byte = buf.view()
    s: [*]byte = buf.span()  // ERROR: cannot create mutable span while read-only view exists
  }

  // 2. Second span while a span is live.
  {
    s1: [*]byte = buf.span()
    s2: [*]byte = buf.span() // ERROR: cannot create second mutable span to same owner
  }
}
```

---

## 5. Slice & Index Syntax

Oak supports Go-like slice syntax, extended with Python-style negative indices. Slices operate on:

* owned arrays `[N]T`,
* views `[]T`,
* spans `[*]T`.

### 5.1. Indexing

```oak
expr[i]
```

* `expr` must have a contiguous sequence type: `[N]T`, `[]T`, or `[*]T`.
* `i` is an integer expression (can be negative).

Index rewriting:

Let `len = length(expr)`.

* If `i >= 0`, then `idx = i`.
* If `i < 0`, then `idx = len + i`.

If `idx` is outside `[0, len)`, behavior is:

* **Safe profile**: trap at runtime (panic/fault), or
* **Explicit API**: use `get(expr, i) -> Option[T]` instead of `expr[i]`.

The exact trap behavior is left to the runtime profile; the language guarantees that out-of-range indexing is an error.

### 5.2. Two-index slicing

Base syntax:

```oak
expr[i:j]   // elements from i (inclusive) to j (exclusive)
expr[i:]    // shorthand for expr[i:len]
expr[:j]    // shorthand for expr[0:j]
expr[:]     // shorthand for expr[0:len]
```

Supported on `[N]T`, `[]T`, `[*]T`.

Index rewriting (Python-style negative indices):

Let `len = length(expr)`.

* If `i` is omitted, treat `i = 0`.
* If `j` is omitted, treat `j = len`.
* If `i < 0`, set `i = len + i`.
* If `j < 0`, set `j = len + j`.

After rewriting, the slice bounds must satisfy `0 <= i <= j <= len`.

If bounds are invalid (`i > j` or any bound outside `[0, len]`), behavior is:

* **Option A (strict)**: runtime trap (safe profile).
* **Option B (explicit)**: use a `try_slice` API that returns `Option[[]T]` / `Option[[*]T]`.

The core language spec leaves the exact choice to profiles, but out-of-range slices must not silently read/write outside the buffer.

### 5.3. Resulting types

Let `T` be the element type of `expr`.

* If `expr: [N]T` and we write `expr[i:j]`, the result type is **read-only view**:

  ```oak
  expr: [N]T
  v: []T = expr[i:j]  // OK
  ```

  By default, slicing an owned array produces a `[]T` (View).

* If `expr: []T`, slicing produces `[]T` (View).

* If `expr: [*]T`, slicing produces `[*]T` (Span).

Writable subslices from an owned array require first creating a span explicitly:

```oak
buf: [128]byte = zero_init()

s: [*]byte = buf.span()
win: [*]byte = s[16:32]
```

This keeps the default slicing of owned arrays read-only and avoids accidental mutation.

### 5.4. Desugaring to `subslice`

The typechecker/borrow-checker can reason about slicing via an abstract desugaring.

#### 5.4.1. Owned arrays

```oak
// expr: [N]T
expr[i:j]
```

behaves like:

```oak
// conceptual desugaring for borrow analysis
{
  tmp: []T = expr.view()        // creates a read-only borrow from expr
  len := length(tmp)
  i' := normalize_index(i, len) // apply negative index rewriting
  j' := normalize_index(j, len)
  subslice(tmp, i', j' - i')    // result: []T
}
```

Borrow checker effect:

* `expr.view()` is a new borrow from `expr` (Rule 4.2.1).
* `subslice` derives within that borrow (no new owner state change).

#### 5.4.2. Views and spans

```oak
v[i:j]  // v: []T
s[i:j]  // s: [*]T
```

behave like:

```oak
subslice(v, i', j' - i')  // []T
subslice(s, i', j' - i')  // [*]T
```

No new borrow is created; the slice shares the same owner as `v`/`s`.

### 5.5. Reverse iteration (Python-style negative step)

Oak reserves the `expr[i:j:k]` syntax for future use. In v1:

* Only two-index slices `expr[i:j]` are defined.
* **Reverse traversal** is done via explicit iterator helpers:

  ```oak
  fn iter_rev[T](v: []T) -> Iterator[T]

  for x in iter_rev(buf[0:len]) {
    /* ... */
  }
  ```

These iterators internally walk the same underlying `View`; they do not require a separate stride field in `View`/`Span`.

The borrow checker treats iterator adaptors as *read-only use* of an existing borrow, with no additional aliasing state.

---

## 6. Interaction with Borrow Checker

Slicing and indexing compose with the borrow model as follows:

1. **Indexing** (`expr[i]`) is a read or write through an existing owner/borrow:

   * For `[N]T` and `[]T`, it is a read.
   * For `[N]T` with `span()` and for `[*]T`, it may be a write.
   * The borrow checker only cares that the underlying borrow state allows a write (no additional rules).

2. **Slicing arrays** (`expr[i:j]` on `[N]T`):

   * Conceptually introduces a single `View` borrow for the duration of the slice's lifetime.
   * Borrow state transitions as in §4.2.1.

3. **Slicing views/spans** (`v[i:j]`, `s[i:j]`):

   * Derived handles that share the same owner and state.
   * No additional borrow state changes.

4. **Lifetimes**:

   * The resulting slices (`[]T` / `[*]T`) follow lexical lifetime rules.
   * They may not escape the block in which they are created (v1).

---

## 7. Optional Region/Capability Tags (Future Extension)

The core spec above does not require region tags, but Oak's type system already supports zero-sized type tags (e.g., for intrusive lists). The same mechanism can be reused for more refined slice capabilities.

Example pattern (not enforced in v1):

```oak
Region: type = interface {}

DefaultRegion: type
RxRegion:      type
TxRegion:      type

View[T, R: Region]: type =
  { base: *T
  , len:  u32
  }

Span[T, R: Region]: type =
  { base: *T
  , len:  u32
  }

// Defaults
[]T  == View[T, DefaultRegion]
[*]T == Span[T, DefaultRegion]

// Domain-specific aliases
RxSpan[T]: type = Span[T, RxRegion]
TxSpan[T]: type = Span[T, TxRegion]
```

The borrow checker itself is **agnostic** to `R`; it continues to enforce "many readers OR one writer" based solely on owners and whether the type is `View` vs `Span`.

Profiles and libraries may use `R` to express additional constraints (e.g., "this API only accepts Tx spans"), but this remains a pure type-level convention.

---

## 8. Limitations & Future Work

* v1 forbids borrows (`[]T` / `[*]T`) from escaping their creation block.

  * Future versions may allow returning views/spans with a simple, explicit lifetime relation (e.g., tied to a parameter).

* Only two-index slicing `expr[i:j]` is supported in v1.

  * Three-index `expr[i:j:k]` and true strided views are reserved for future extensions.

* Error behavior for out-of-range slices is left to profiles:

  * A **safe profile** should trap.
  * A **systems profile** may prefer explicit `try_slice` APIs that return `Option`.

* The borrow checker does not attempt to prove disjointness of subslices; all slices of the same owner are conservatively assumed to potentially overlap.

This spec is intentionally small but expressive enough to:

* build non-allocating parsers and state machines,
* manage DMA buffers safely,
* and compile down to straightforward, readable C that any firmware engineer can understand.
