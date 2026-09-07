# Intrusive Containers

An intrusive container stores its link structure *inside* the elements —
Linux's `struct list_head`, Serenity's `IntrusiveList<T, &T::m_node>`,
Fuchsia's `fbl::DoublyLinkedList`. Kernels use them because membership
costs no allocation and removal is O(1) from the element itself. The cost
in C/C++ is severe: the links are raw pointers, the container has no idea
what it points at (`container_of` exists to reconstruct the containing
object from a link address), and nothing checks liveness, aliasing, or
even that a node isn't on two queues that both think they own it.

## The Oak doctrine: pools and typed index links

Oak does not imitate the pointer form. The doctrine (surveyed against all
three kernels in `docs/notes/os-structures-survey.md`) is:

> **Elements live in static pools. Links are typed indices into the pool.
> A sentinel index is the null.**

```oak
Thread: type = struct {
  priority: u8
  next: u32
  prev: u32
}

pool: [8]Thread
readyHead: u32 = 255   // sentinel: not linked
```

Executed end to end — enqueue, unlink-from-middle, dequeue —
in `compiler/e2e_scheduler_test.go`.

## Why the index form dominates the pointer form

| Property | `list_head` (pointers) | Oak pool + indices |
| --- | --- | --- |
| identity recovery | `container_of` macro arithmetic | the index *is* the identity |
| link size | 8 bytes per direction | 1–4 bytes (`u8`/`u16`/`u32`) — denser nodes, better cache lines |
| dangling links | undefined behavior | impossible to *dereference outside the pool*: every hop is bounds-checked (or provably in range) |
| stale links | undetectable | detectable: generational handles (index + generation counter) make use-after-free a checked failure |
| allocation | element embeds node, but elements themselves are usually kmalloc'd | pool is static — Power-of-Ten rule 3 by construction |
| serialization / DST | pointer graphs don't serialize | index graphs are position-independent: snapshot the pool, replay deterministically |

The bounds trap per hop is the honest cost. The recorded optimization
path is elision-by-proof: an index that the discipline layer already
proves in-range (a canonical bounded loop over the pool, a link stored
only from checked values) does not need a second dynamic check.

## The hierarchy of intrusive shapes

Ordered by link count per element:

1. **Free list / stack** — one link (`next`): allocation pools.
2. **Singly linked queue** — one link + tail cursor: MPSC mailboxes.
3. **Doubly linked list** — two links: ready queues, LRU, anything with
   O(1) middle removal (the executed example).
4. **Trees** — three links (children + parent) or two + parent-in-tag:
   rbtree/WAVL-style ordered structures (Fuchsia schedules and indexes
   handles with a WAVL tree). Same doctrine, more links; loop form with
   parent links avoids recursion, fitting the discipline profile.
5. **Multi-membership** — an element carrying *several* node structs
   (Linux tasks sit on run queues and wait queues simultaneously) is just
   several typed index fields; the type system keeps queue A's links from
   being used as queue B's, which the pointer form cannot.

## What's still missing

Reusable intrusive *libraries* need generic functions
(`unlink[T, N](pool: [*]T, id: u32)` does not monomorphize yet) — the top
item on the gap list. Enforced single-membership (an element cannot be
enqueued twice) is a typestate/resource-types question (`OAK-B0111`);
today it is an invariant you assert, which is still one rung better than
the kernels this chapter surveyed, where it is an invariant you hope.
