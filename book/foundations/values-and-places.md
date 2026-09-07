# Values and Places

The oldest distinction in systems programming is the one C spells
*rvalue* versus *lvalue*: some expressions name a **value** (something you
can read), and some name a **place** (somewhere a value lives, which you
can also assign). Most memory-safety failures are place errors — writing
through a place that no longer exists, or that someone else is reading.
Oak makes the distinction structural instead of conventional.

## Every expression yields a value

`a + b`, `f(x)`, `cond ? x | y`, `Point { x: 1, y: 2 }` — expressions
evaluate to values. Values are copied where used (v1 owned aggregates are
explicit-cost copies; `docs/spec/50-borrowing.md` §8 records the decision),
and a value has no address you can talk about: Oak has no `&value` of a
temporary, no pointer arithmetic, no way to smuggle a value's storage out
of its expression.

## Places are enumerated, not inferred

A **place** is exactly one of:

| Place | Example | Assignable? |
| --- | --- | --- |
| a local binding | `count` | `count = e` |
| a static global | `pool` | `pool = e` (constant-initialized at rest) |
| an owned-array element | `buf[i]` | bounds-checked store |
| a span element | `s[i]` | bounds-checked store; **views are not places for writing** |
| a record field path | `ring.head`, `pool[i].next` | field store through checked path |

Everything else — call results, literals, match results, arithmetic — is a
value. The two directions have different machinery all the way down to the
emitted C:

- **Reads** lower through *rvalue* forms: `oak_index(base, len, i)` is a
  bounds-checked ternary that produces a value.
- **Writes** lower through *lvalue paths*: `pool[ oak_lv_idx(i, len) ].next
  = v` keeps the whole access path assignable while every index in it is
  checked (trap, never UB). The compiler refuses to conflate them — an
  rvalue form in assignment position is a compile-breaking marker, not a
  cast.

Executed: `compiler/e2e_scheduler_test.go` assigns through
`pool[pool[id].prev].next` — a three-deep checked lvalue path.

## Borrows are views of places

`view(&owner)` and `span(&owner)` do not create pointers; they create
**typed access to a place** with the aliasing laws of
`docs/spec/50-borrowing.md`: any number of readers (`[]T`) or exclusive
writers (`[*]T`, with region-disjoint siblings), never both, never
escaping the owner's scope (`OAK-B0109`). A view is a place you may read;
a span is a place you may also write; the borrow checker is the machine
that decides which places are *currently* allowed to be either. The laws
are proven in `Oak.Borrowing`/`Oak.Reborrow`, and the compiler's admission
procedures are machine-checked transliterations
(`Oak.BorrowStateRefinement`, `Oak.ReborrowRefinement`).

## Temporaries are compiler business

When a value needs a transient place — matching directly on a call result,
a value-producing conditional with statement branches — the compiler
manufactures the temporary itself (a hoisted scrutinee, a
declaration-plus-branch-assignment) and the surface language never sees
it. You cannot name a temporary, so you cannot keep one alive. That is the
whole rvalue/lvalue doctrine in one sentence: **values are yours to
compute, places are yours only by declaration or by borrow, and the
compiler owns everything in between.**
