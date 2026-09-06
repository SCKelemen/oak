from pathlib import Path

path = Path("docs/LANGUAGE_MODEL.md")
s = path.read_text()

intro = '''Oak is a systems language in which one checked semantic definition should drive every projection that can soundly reuse it.

> Define a fact once; project it many ways.
'''
constitution = '''Oak is a systems language in which one checked semantic definition should drive every projection that can soundly reuse it.

## Language constitution

Oak optimizes for, in order:

1. **Correctness**
2. **Performance**
3. **Simplicity**

Simplicity is pursued aggressively when it does not weaken correctness or materially compromise performance.

**Safety and ergonomics are cross-cutting constraints.** Oak should be safe by default, make unsafe boundaries narrow and explicit, expose runtime cost rather than hide it, and keep the common path pleasant to read and write.

The syntactic surface should stay tight, lightweight, and orthogonal. Prefer composition from a small set of powerful constructs—records, ADTs (and GADT-style refinements as the type system grows), functions, generics, and pattern matching—over adding a special form for every domain concept. New syntax must earn its place by expressing semantics that cannot be composed cleanly from existing constructs.

Layout and brace syntax are equivalent spellings of the same language. Ergonomic sugar may shorten programs, but it may not create a second semantic model.

> Define a fact once; project it many ways.
'''
if s.count(intro) != 1:
    raise RuntimeError("language-model introduction changed")
s = s.replace(intro, constitution, 1)

unsafe = '''Unsafe primitives should eventually state the assumptions they introduce so that higher-level code can contain and discharge those assumptions explicitly.

## 4. Proposition: what facts are known?
'''
allocation = '''Unsafe primitives should eventually state the assumptions they introduce so that higher-level code can contain and discharge those assumptions explicitly.

### Allocation is explicit semantic behavior

Oak has no hidden allocation. APIs should prefer, roughly in this order:

```text
stack/static storage
caller-provided buffers
arenas / regions
bounded typed slabs / pools
specialized allocators
explicit general heap allocation
```

The ordering is a design preference, not a requirement that every object use an arena or slab. Allocation strategy follows lifetime and proof obligations.

The surface language should not need bespoke allocator statements. These are ordinary types whose parameters carry semantic facts:

```oak
Arena[R]
Slab[T, N]
Handle[T]
```

`Arena[R]` groups lifetime under a region identity `R`. Values tied to `R` must not escape that lifetime without an explicit ownership transition.

`Slab[T, N]` is a bounded homogeneous pool. Its capacity is part of the semantic model and can participate in bounds/resource proofs.

`Handle[T]` is stable object identity rather than an allocation mechanism. A generational implementation can prove that stale generations do not resolve to newly reused slots.

Allocation itself is an effect. Conceptually:

```oak
fn build[R](arena: Arena[R]) -> Graph[R]
  effects { Memory.Allocate[arena] }
```

A broad prohibition applies to all scoped instances:

```oak
realtime fn process(...)
  forbids { Memory.Allocate, Thread.Block, Os.Syscall }
```

Thus realtime/no-allocation requirements are checked semantic facts rather than comments. Generic dispatch, matching, conversions, and interface constraints may not introduce allocation invisibly.

## 4. Proposition: what facts are known?
'''
if s.count(unsafe) != 1:
    raise RuntimeError("unsafe/proposition boundary changed")
s = s.replace(unsafe, allocation, 1)

old = '''For example, the current syntax AST historically stores record fields in a Go map. A backend may not invent a deterministic machine field order from that map and claim it is source layout. Exact representation facts become available only after the syntax/typed AST preserves the ordering needed to justify them.
'''
new = '''For example, record syntax now preserves field source order separately from its fast name-lookup map. That justifies ordered semantic field membership, but it still does not justify target ABI offsets. Exact representation facts become available only after a target layout pass computes size, alignment, padding, and offsets.
'''
if s.count(old) != 1:
    raise RuntimeError("record fail-closed paragraph changed")
s = s.replace(old, new, 1)

path.write_text(s)
