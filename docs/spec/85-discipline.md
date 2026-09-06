# Program Discipline Profiles

Oak's target programs are written in the tradition of MISRA C, NASA's Power
of Ten, and TigerBeetle's TigerStyle: statically bounded execution, static
allocation, dense assertions, and zero tolerated warnings. This chapter
defines discipline **profiles** — named sets of statically checked rules —
so that discipline is a compiler-enforced property of a program, not a
convention in a style guide.

Discipline rules follow the constitution: they are semantic facts checked by
the compiler with stable diagnostic codes (`OAK-D01xx`), not new syntax.

## 1. Profiles

- **default** — the discipline analyses run and report, but only rules that
  protect soundness are errors.
- **strict** — every rule in this chapter is enforced; warnings are treated
  as rejections (zero-warning policy).

Profile selection is a build-level concern; its surface (manifest field,
compiler flag) is not yet frozen.

## 2. Bounded call depth: safe recursion

Oak does not ban recursion; it requires recursion to be **safe**: stack
depth must be statically bounded.

A call is a **tail call** when it is the last action of a function body —
the body's result expression, the trailing expression of a block body, or
the body of a match arm in result position. Tail calls are required to cost
no stack frame: the compiler lowers them to loops (or, for mutual recursion,
trampolines) rather than trusting a downstream C compiler to do so.

Acceptance is certificate-based. The compiler ranks the call graph by
strongly connected components: ranks must strictly decrease across every
stack-consuming call and never increase across a tail call. `Oak.Discipline`
proves that under this certificate the stack depth of any call chain — of
any length, including unbounded tail loops — is at most the start's rank,
and that every call cycle in an accepted graph is tail-only, hence
eliminable.

Current enforcement:

- Direct self tail recursion whose only self call is the body's result
  invocation **compiles to a loop** in the C backend (parameter rebinding
  plus `continue` in a `while (1)` frame): accepted silently, genuinely
  constant-stack.
- Mutual tail recursion whose members share one signature (types and
  parameter names) and whose member calls all sit in result position
  **compiles to a trampoline**: one engine function with a state tag per
  member, tail calls between members becoming state switches inside a
  single frame, and thin wrappers preserving each member's identity. This
  is the cooperative state-machine / superloop shape of embedded firmware.
- Tail-only cycles the backend does not lower yet (mismatched signatures,
  tail calls inside match arms) are accepted with the recorded obligation
  `OAK-D0102` (warning): eliminable in principle, elimination not yet
  guaranteed. Strict profile treats this as a rejection until lowering
  lands.
- Cycles containing any stack-consuming call are rejected: `OAK-D0101`.

Planned extensions: declared recursion depth bounds (a semantic fact that
converts a stack cycle into a bounded obligation with a runtime check when
not statically discharged), trampoline lowering for mismatched-signature
groups and for tail calls in match-arm position.

## 3. Bounded loops

Every loop must have a statically evident bound (Power of Ten rule 2).
Planned enforcement: a loop bound is a semantic fact (constant trip count,
structural recursion over a finite sequence, or a declared bound with a
checked runtime guard). `while` loops without an evident bound will be
rejected in the strict profile. Not yet enforced.

## 4. Allocation phase

No dynamic allocation after initialization (Power of Ten rule 3,
TigerStyle static allocation). Oak's allocation story is already explicit —
arenas, slabs, pools, and handles with declared capacities
(`60-effects-allocation`) — and allocation is an effect
(`Memory/Allocate`). Planned enforcement: the strict profile partitions the
program into an initialization phase and a steady state; functions reachable
from the steady state must not carry unscoped allocation effects. Not yet
enforced.

## 5. Assertions

TigerStyle assertion density: functions assert their arguments, results, and
invariants; assertions are compiled in, not compiled out. The `assert`
builtin exists: it takes one `Bool`, returns unit, evaluates in the
interpreter, and lowers to an always-on C helper (`__builtin_trap` on
failure) that no build mode elides. Planned: feeding assert conditions into
the proposition axis (statically discharged assertions become proofs) and a
strict-profile density lint.

## 6. Checked results

A non-unit result must be consumed or explicitly discarded (Power of Ten
rule 7). Planned: unused-result diagnostic with an explicit discard form.
Not yet enforced.

## 7. Zero warnings

The strict profile promotes every warning — including recorded unsafe
assumptions (`OAK-B0110`) and tail-recursion obligations (`OAK-D0102`) — to
a rejection. Auditable assumptions remain expressible; silently accumulated
ones do not.

## 8. Formal verification targets

- rank certificate bounds stack depth (`Oak.Discipline.stack_depth_bounded`) — proved;
- accepted cycles are tail-only (`Oak.Discipline.cycle_is_all_tail`) — proved;
- loop-bound and allocation-phase laws — to be formalized with their
  enforcement.
