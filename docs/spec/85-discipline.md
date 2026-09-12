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

Profile selection is a build-level concern, carried by
`compiler.Options.Profile` (`WithProfile("strict")`) and on the command line
by `-profile`:

```text
oak build -profile strict [-o out.c] [dir]
oak run   -profile strict [dir]
oak test  -profile strict [flags] [dir]
```

The flag accepts `default` and `strict`; anything else is a usage error. The
REPL's `:strict` toggles the same option for a session. The compile pipeline
gates on type checking, borrow checking, and discipline analysis: error
diagnostics always reject, and the strict profile also rejects every warning
(section 7).

**Profiles are per module.** A profile is a property of the code being
judged, and a dependency's discipline is its own business: a strict root is
not blocked by a warning inside a library it imports, and a library can
promise strictness to its importers. The manifest directive
`profile <default|strict>` (`83-modules.md` §4.1) sets the profile every
package of that module is judged under. The rule the pipeline gate applies
to a warning is: **find the package that owns the warning's primary cause,
then that package's module, then that module's profile**; the warning
rejects exactly when the profile is strict. Concretely:

| Owner of the warning | Effective profile |
| --- | --- |
| the root package, a package of the root module, or any package outside every module (a single-source build, a REPL session without `oak.mod`) | `-profile` when given, else the root manifest's `profile`, else `default` |
| a package of a dependency module | that module's `profile`, else `default` |
| the spliced bootstrap library (`import(std)`, `import(testing)`) or a standard library package | `default` — the standard library has no manifest and is judged by its own tests |
| a monomorphized clone of a generic function (stamped with its instantiation, not a package) | the root profile, so a strict root never loses a warning to a missing stamp |

Errors reject regardless of profile. `-profile strict` on a program that
imports the prelude therefore judges the program's own packages strictly
while the prelude's remaining non-canonical loops (section 3) are reported,
not fatal; making the prelude itself strict-clean is the standard library's
own obligation and is tracked in `docs/notes/ml-feedback-2026-09.md`.

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

- Direct self tail recursion whose self calls all sit at lowerable tail
  sites **compiles to a loop** in the C backend (parameter rebinding plus
  `continue` in a `while (1)` frame): accepted silently, genuinely
  constant-stack. Lowerable tail sites are the body result, block trailing
  expressions, and the arms of result-position matches over an identifier
  scrutinee with literal/wildcard patterns — so terminating recursion
  (base case + tail call) lowers, with base-case arms becoming guarded
  returns.
- Mutual tail recursion whose members share one signature (types and
  parameter names) and whose member calls all sit in result position
  **compiles to a trampoline**: one engine function with a state tag per
  member, tail calls between members becoming state switches inside a
  single frame, and thin wrappers preserving each member's identity. This
  is the cooperative state-machine / superloop shape of embedded firmware.
- Tail-only cycles the backend does not lower yet (mismatched signatures,
  binding/variant-pattern arms, non-identifier scrutinees) are accepted
  with the recorded obligation
  `OAK-D0102` (warning): eliminable in principle, elimination not yet
  guaranteed. Strict profile treats this as a rejection until lowering
  lands.
- Cycles containing any stack-consuming call are rejected: `OAK-D0101`.

Planned extensions: declared recursion depth bounds (a semantic fact that
converts a stack cycle into a bounded obligation with a runtime check when
not statically discharged), trampoline lowering for
mismatched-signature groups, and lowering for binding/variant-pattern arms.

## 3. Bounded loops

Every loop must have a statically evident bound (Power of Ten rule 2).
Enforced: the canonical bounded counter shape — `while i < bound` (or `<=`)
advancing `i` exactly once per iteration by a positive constant, with the
bound an integer constant or an identifier the body never reassigns — is
recognized as carrying its own bound (`Oak.BoundedLoop` proves such a loop
runs at most `bound - i` iterations). Every other `while` records the
obligation `OAK-D0103` (warning), which the strict profile rejects.

A loop the recognizer rejects is an `OAK-D0103` obligation. The REPL's
`:lean <file>` states it as a termination theorem over `Oak.Loops` — the
loop's guard and body translated into a semantics with explicit wrap-around —
and `Oak.Loops.ranking_terminates` is the law that discharges it: exhibit a
`Nat`-valued rank that strictly decreases across every guarded step
(`docs/spec/83-modules.md` section 10).

An **integer constant** in the step or the bound is an integer literal or an
integer-type constructor applied to one integer literal: `k = k + 1` and
`k = k + u32(1)` are the same step, and `while k < 10` and
`while k < u32(10)` the same bound, exactly as `25-type-inference.md` §3a
makes them the same expression. The discipline analysis runs before
literal typing would fold the constructor, so it recognizes the constructor
itself; a constructor over anything but a literal is not a constant.

The `OAK-D0103` record names the enclosing function in its title, points its
primary label at the `while` statement, and says which part of the canonical
shape the loop misses — the condition, the bound, a missing or doubled
advance, or a non-constant step:

```text
warning[OAK-D0103]: stdlib.oak:348:7: loop in bytes_move_within has no statically evident bound
  = primary: the step is not `i = i + k` with k a positive constant
```

Planned extensions: declared bounds with checked runtime guards, and
structural iteration over finite sequences.

### 3a. `break`

`break` leaves the innermost enclosing `while`; it is legal only inside a
loop body (a function literal starts a fresh scope, so a break inside one
cannot leave a loop outside it — `break outside a while loop` otherwise).
A bounded loop that breaks early is still bounded: the canonical shape
certifies an upper bound on iterations, and leaving sooner cannot exceed
it, so the strict profile accepts a break in a certified loop unchanged.
The backends agree by construction — statement-position conditionals lower
to `if`/`else` and loops to `while`, so C's `break` leaves exactly the Oak
loop, and the interpreter consumes the break at the loop it belongs to.

## 4. Allocation phase

No dynamic allocation after initialization (Power of Ten rule 3,
TigerStyle static allocation). Oak's allocation story is already explicit —
arenas, slabs, pools, and handles with declared capacities
(`60-effects-allocation`) — and allocation is an effect
(`Memory.Allocate`). The phase split is expressed and enforced through
effect clauses (`60-effects-allocation` §2): every steady-state entry point
— the event loop, request handlers, interrupt paths — declares
`forbids { Memory.Allocate }`, and the compiler rejects any allocation
reachable from it through the call graph, naming the path. Initialization
code is whatever those entry points do not reach; the compiler infers no
phase. Externs that allocate must declare `effects { Memory.Allocate }`; an
undeclared extern under a forbidding entry point is itself a rejection, so
an allocation cannot hide behind a foreign call.

The rule is stated once in the module manifest (`83-modules.md` section
4.1): each `steady <package-path> <function>` line names a steady-state
entry point of a package of this module, and the compiler checks it exactly
as if it declared `forbids { Memory.Allocate }`, keeping any clause it
declares itself. Findings carry `OAK-E0104` with the entry point, the
directive spelling, and the call path to the allocation or to the site
whose effects cannot be known. An entry that names a package outside the
module or a function that does not exist fails the build (`OAK-M0112`)
rather than forbidding nothing. The per-function clause remains the manual
form for a hot path that is not an entry point.

## 5. Assertions

A failed assertion is attributable: the C lowering passes the Oak source
file and line, and a hosted build prints `oak: assertion failed at file:line`
to stderr before the trap. Freestanding builds (`-ffreestanding`, or
`-DOAK_FREESTANDING`) keep the bare trap and take no libc dependency.

**Assertions that name both values.** `assert_eq(got, want)` and
`assert_ne(got, want)` take two values of one type — a fixed-width integer
(aliases and the platform-sized names resolve to their width), `f32`, `f64`,
or `Bool` — and trap exactly when the comparison fails. A hosted build prints
`oak: assertion failed at file:line: got 5, want 4` (or `want anything but 7`
for `assert_ne`) before the trap; integers print in decimal in their own
signedness, `Bool` as `true`/`false`, floats with enough digits to round-trip
(`%.9g` for `f32`, `%.17g` for `f64`) so the message identifies the exact
value rather than a rounded reading of it. Freestanding builds keep the bare
trap. The operands must share one of those types: `OAK-T0601` rejects a
width or integer/float mismatch (there is no implicit promotion) and any
operand the message could not print (records, views, strings — assert on a
field or element, or use `assert` with a `Bool`). The interpreter evaluates
both forms with the same message; the Lean extraction models them as the
trap alone (`none` when the comparison fails), not the printed values. The
`testing` prelude's `test_check_eq_*`/`test_check_ne_*` are the counterpart
for property tests (`110-testing.md`): the failure keeps its invariant id as
the signature and carries the values to the runner.

TigerStyle assertion density: functions assert their arguments, results, and
invariants; assertions are compiled in, not compiled out. The `assert`
builtin exists: it takes one `Bool`, returns unit, evaluates in the
interpreter, and lowers to an always-on C helper (`__builtin_trap` on
failure) that no build mode elides. Planned: feeding assert conditions into
the proposition axis (statically discharged assertions become proofs) and a
strict-profile density lint.

## 6. Checked results

A non-unit result must be consumed or explicitly discarded (Power of Ten
rule 7).

**The discard form** is implemented: `_ = expr` evaluates `expr` for its
effects and drops its result on purpose. `_` binds nothing and is never a
variable; the statement is an expression statement marked as a discard.
Discarding a unit-typed expression is rejected (the form would say nothing),
so every `_ =` in a program marks a real value the author chose to ignore —
typically the status result of an extern binding:

```oak
_ = putchar(c.Int(10))       // putchar returns c.Int; we do not care
```

**The unused-result rule** is planned: `OAK-D0104` (warning) for an
expression statement whose non-unit result is neither consumed nor
discarded, rejected by the strict profile. The discard form exists first so
that the rule, when it lands, has an answer to point at. Until then a bare
`putchar(c.Int(10))` is accepted silently.

## 7. Zero warnings

The strict profile promotes every warning — including recorded unsafe
assumptions (`OAK-B0110`) and tail-recursion obligations (`OAK-D0102`) — to
a rejection. Auditable assumptions remain expressible; silently accumulated
ones do not.

**Admitted assumptions.** A module may state, once and in the open, which
recorded assumptions it accepts: `admit <code>` in its `oak.mod`
(`83-modules.md` section 4.1). Under the strict profile an admitted
assumption is not promoted to a rejection; everything else about it is
unchanged — it is still recorded, `oak vet` and the REPL's `:obligations`
still list it (marked "admitted by oak.mod"), and `:lean` still states it,
so the audit trail is exactly as long as before and the acceptance is a
reviewable line in the manifest rather than a weaker profile. Only the
recorded assumptions are admissible — `OAK-B0110` (an unsafe block's
writable-disjointness or foreign-buffer contract, `92-ffi.md` section 2.7),
`OAK-B0122` (an unsafe block's foreign-function-pointer contract, `c.fn_at`,
`92-ffi.md` section 2.10), `OAK-D0102` (a tail-recursion obligation),
`OAK-D0103` (a loop without a static bound); an error code, or a warning
that is not an assumption, fails the manifest (`OAK-M0112`). Admissions are per module, like profiles: a
dependency's manifest speaks for its own packages and the root's for the
root's; the command-line `-profile` flag grants none, and a single-source
build has no manifest and admits nothing. The motivating case (ml finding
F22): a strict module that borrows runtime memory through `c.borrow` records
the foreign-buffer contract as `OAK-B0110` on every borrow, so without an
admission no strict module could use tier 4 of the FFI at all.

## 8. Formal verification targets

- rank certificate bounds stack depth (`Oak.Discipline.stack_depth_bounded`) — proved;
- accepted cycles are tail-only (`Oak.Discipline.cycle_is_all_tail`) — proved;
- bounded counter loops admit at most `bound - start` iterations
  (`Oak.BoundedLoop.trace_bounded`) — proved;
- allocation-phase laws — to be formalized with their enforcement.
