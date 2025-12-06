# Oak Type Universe

This document defines the **semantic model of types** in Oak:

* What a type *is* (as a set of values).
* The core special types: `never`, `Unit`/`()`, `Any`.
* How **subtyping** works as a partial order.
* How **union**, **intersection**, and **record/shape** types fit into that order.
* How this model stays compatible with our goals: MCU-friendly, C-like codegen, and a tractable typechecker.

The goal is **clarity and correctness**: a small, principled core that explains all the language features we’ve designed so far.

---

## 1. Types as sets of values

Conceptually, every type in Oak denotes a (possibly empty, possibly infinite) **set of values**.

* `u8` is the set `{ 0u8, 1u8, ..., 255u8 }`.
* `Bool` (implemented as a sum/union type) is the set `{ .False, .True }`.
* `Unit` (a.k.a. `()` or `{}`) is a singleton set containing one value:

  * Conceptually: `{ () }` or `{ {} }`.
* `never` is the **empty set**: it has no inhabitants.

We write `[[ T ]]` for “the semantic set of values of type `T`”.

---

## 2. Special types: `never`, `Unit`, `Any`

### 2.1 `never` – uninhabited bottom

`never` is the type with **no values**:

* `[[ never ]] = ∅`.
* It is used for expressions that **cannot produce a value**:

  * A function that always aborts, loops forever, or otherwise never returns can be typed as returning `never`.

Subtyping:

* For **any** type `T`, we consider `never` a subtype of `T`:

  * `never ≤ T`.
* Intuition: "If something of type `never` existed, it would also be valid where `T` is expected, because there are no counterexamples." This is the standard construction of a **bottom** element in a subtype lattice.

### 2.2 `Unit` / `()` / `{}` – singleton type

`Unit` is the **unit type**, with exactly one value:

* `Unit: type = {}` (empty record / empty struct).
* Syntactic sugar: `()` is another spelling of `Unit`.
* Semantics: `[[ Unit ]]` has exactly one element.

We treat:

* `{}` (empty record type), `Unit`, and `()` as **the same type** up to canonicalization.

`Unit` is **not** the bottom of subtyping (that’s `never`), but it is the **least informative inhabited type**:

* It carries no information except “this computation terminated successfully”.

Examples:

* Procedures that conceptually "return nothing" are typed as returning `Unit`.
* In the C backend, `Unit` may be compiled as `void` or as an empty struct, depending on ABI needs.

### 2.3 `Any` – optional top

`Any` is an **optional** top type:

* Intended meaning: `[[ Any ]]` is the union of all representable values in the language (across all types).
* Subtyping: For any type `T`, `T ≤ Any`.

We keep `Any` **heavily controlled** because:

* It behaves like a dynamic “erase type information” bucket.
* MCU-focused code often doesn’t need it, and we want to preserve predictable layouts and simple codegen.

Implementation guidance:

* The core compiler and standard library should not rely on `Any` to model fundamental constructs.
* If introduced, `Any` is largely confined to FFI boundaries, reflection, or debugging utilities.

---

## 3. Subtyping as a partial order

We define a **subtyping relation** `≤` over types, forming a partial order.

> Read `A ≤ B` as: “Every value of type `A` can be used where a `B` is expected, without runtime checks or errors.”

Basic properties:

* **Reflexive**: `T ≤ T`.
* **Transitive**: If `A ≤ B` and `B ≤ C`, then `A ≤ C`.
* **Antisymmetric**: If `A ≤ B` and `B ≤ A`, then `A` and `B` are considered **equivalent types** (same canonical type).

Anchors:

* `never ≤ T` for all `T` (bottom).
* For all `T`, `T ≤ Any` if `Any` is enabled (top).

### 3.1 Nominal types vs structural relations

Oak is **nominal** by default:

```oak
Foo: type = struct{ x: u8 }
Bar: type = struct{ x: u8 }
```

* `Foo` and `Bar` are distinct types by **name**, even though they have the same shape.
* There is **no automatic subtyping** `Foo ≤ Bar` or `Bar ≤ Foo` just because their fields line up.

But the compiler also maintains **canonical structural shapes** for types (especially records), which we use in specific places:

* Pattern matching type annotations.
* Shape-based constraints and interfaces.

This gives us:

* A clear nominal story for layout and C codegen.
* Room for structural reasoning where it’s needed, without collapsing all types into one big structural lattice.

---

## 4. Union and intersection types

### 4.1 Union types: `A | B`

A union type `A | B` is the **disjoint sum** of the value sets of `A` and `B`:

* `[[ A | B ]] = [[ A ]] ∪ [[ B ]]`.

Subtyping:

* `A ≤ A | B` and `B ≤ A | B`.
* More generally, if `A₁ ≤ B₁` and `A₂ ≤ B₂`, then:

  * `A₁ | A₂ ≤ B₁ | B₂`.

In the subtype lattice, `A | B` is the **least upper bound** (join) of `A` and `B`, when we ignore `Any` and `never`.

Usage in Oak:

* ADTs and sum-like types use unions under the hood.
* Pattern matching on `A | B` narrows the type based on the branch.

### 4.2 Intersection types: `A & B`

An intersection type `A & B` represents values that are **both** `A` and `B`:

* Intuitively: `[[ A & B ]] = [[ A ]] ∩ [[ B ]]`.
* Operationally in Oak, we use intersections mainly at the **type layer** for:

  * Record/shape composition (`Point2d & { z: u8 }`).
  * Interface/constraint composition (`K: Eq[K] & HashKey[K]`).

Subtyping:

* `A & B ≤ A` and `A & B ≤ B`.
* If `C ≤ A` and `C ≤ B`, then `C ≤ A & B`.

So `A & B` is the **greatest lower bound** (meet) of `A` and `B` where it’s defined.

Implementation in Oak:

* For records, `A & B` is canonicalized into a single *merged* record shape, if and only if there are no conflicting field types.
* For interfaces/constraints, `Eq[T] & HashKey[T]` means “T must satisfy both interfaces at once.”

---

## 5. Record/shape types and `Unit`

### 5.1 Records as products

A record or struct type is a **finite product** of fields:

```oak
{ x: u8, y: u8 }
```

Semantically:

* `[[ { x: u8, y: u8 } ]] = [[ u8 ]] × [[ u8 ]]`.

Oak canonicalizes record types into a standard form:

* Fields sorted / ordered deterministically.
* Intersections like `{ x: u8 } & { y: u8 }` become `{ x: u8, y: u8 }`.
* Conflicting field definitions → type error.

### 5.2 Empty record and unit

The empty record type:

```oak
{}
```

is the product over zero fields, which yields a singleton set. We treat:

* `{}`
* `Unit`
* `()`

as **equivalent types** (same canonical type): the **unit type**.

So:

* `[[ {} ]] = [[ Unit ]] = [[ () ]]` is a singleton.
* `never ≤ Unit` because `never` is bottom.

### 5.3 Shape equivalence vs nominal identity

Example:

```oak
Point2d: type = { x: u8, y: u8 }
Point3d: type = Point2d & { z: u8 }
```

Canonical shapes:

* `shape(Point2d) = struct{ x: u8, y: u8 }`.
* `shape(Point3d) = struct{ x: u8, y: u8, z: u8 }`.

`Point2d` and `{ x: u8, y: u8 }` share the same shape but remain **nominally distinct types** unless we’re in a context that uses shape equivalence (like pattern matching or shape constraints).

---

## 6. Extensible record constraints (reserved)

We reserve notation for **"at least these fields"** constraints without activating it yet.

Idea:

```oak
Yu8: type = { y: u8 }

fn get_y(val: >Yu8) -> u8
  val.y
```

Reading:

* `>Yu8` means: any type whose canonical record shape has **at least** the field `y: u8` (possibly more fields).

Similarly:

```oak
fn get_x(value: >{ x: u8 }) -> u8
  value.x
```

would accept `Point2d`, `Point3d`, and any other record type with at least field `x: u8`.

Status:

* This is **not** part of the current core type system.
* It is reserved in the design so we can later introduce width-subtyping for records **locally**, without changing the nominal core.

For now, all record types used as plain annotations are treated as **exact shapes**.

---

## 7. Interfaces and the type universe

Interfaces live purely in the **type layer** and behave like **structural constraints** on method sets.

Example:

```oak
Eq[T]: interface =
  fn (self: *T, other: *T) -> Comparison

HashKey[T]: interface =
  fn (self: *T) hash() -> u64

Map[K: Eq[K] & HashKey[K], V]: type = struct{
  -- ...
}
```

A concrete type `T` **satisfies** `Eq[T]` if its method set contains a method with the required signature.

* There is no runtime representation of interfaces.
* At the type level, they contribute to subtyping by constraining which type arguments are allowed.
* At codegen time, interfaces are erased; monomorphized code sees concrete types and functions.

In the semantic model, we can think of an interface applied to `T` as a **predicate** over types, not as a separate value set.

---

## 8. Summary

1. **Types as sets**

   * Each type denotes a set of values: `[[ T ]]`.

2. **Special types**

   * `never`: uninhabited bottom, `[[ never ]] = ∅`, and `never ≤ T` for all `T`.
   * `Unit` / `()` / `{}`: singleton unit type, `[[ Unit ]]` has one value.
   * `Any`: optional top, with `T ≤ Any` for all `T`.

3. **Subtyping partial order**

   * `≤` is reflexive, transitive, antisymmetric.
   * Union `A | B` acts as a join (least upper bound) when defined.
   * Intersection `A & B` acts as a meet (greatest lower bound) when defined.

4. **Records and shapes**

   * Record types are products of fields; empty record `{}` is unit.
   * Canonicalization merges intersections; conflicting fields error.
   * Shape equivalence is used in pattern matching and constraints, but nominal types remain distinct for layout and C codegen.

5. **Extensible record constraints (reserved)**

   * Potential `>Shape` notation for "has at least these fields".
   * Not yet active; kept as a future extension point.

6. **Interfaces**

   * Structural constraints over method sets.
   * Used for implicit interface satisfaction and generic bounds.
   * Erased at codegen; only concrete types reach the C backend.

This model keeps the **theory clean** (sets + partial order + joins/meets where needed) while staying aligned with Oak’s pragmatic goals: **fast compilation, simple MCU-friendly C output, and enough richness for safe APIs, ADTs, and intrusive data structures.**
