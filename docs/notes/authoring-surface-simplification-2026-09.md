# Note: simplifying Oak's authoring surface without weakening the language

**Status: design audit and proposal, non-normative.** 2026-09-15,
`specification` branch at `5419d818`. This note reviews the specified language,
the parser, and the checked-in Oak corpus. It proposes a smaller canonical
authoring surface while preserving Oak's functionality, correctness,
representations, proof obligations, and performance model. No syntax or
semantics changes merely by appearing here.

## Conclusion

Oak's semantic core is already comparatively small and coherent. Its
authoring surface is not. Several independent syntax families express the
same semantic operation, while a few semantic facts are distributed across
different mechanisms instead of living in the type that owns them.

The largest opportunities are:

1. publish one canonical dialect and treat every other spelling as temporary
   compatibility input;
2. remove the ambiguous `Name := A | B` ADT shorthand;
3. separate Boolean conditionals from pattern matching at the surface while
   continuing to lower both to the same match core;
4. choose one declaration grammar for functions;
5. add an allocation-free structural `for` that lowers to the existing
   counted `while` form;
6. use expected types to remove redundant numeric literal constructors and
   collapse the combinatorial conversion-name family;
7. make effects, parameter modes, and result provenance properties of
   callable types instead of partly trusted side facts; and
8. unify compile-time structural records, interfaces, and sealing signatures
   without merging them with runtime `struct` representations.

The proposal does **not** remove distinctions that carry safety or machine
meaning. Owners, views, spans, checked and unchecked conversions, layout
facts, effects, protocols, laws, literal projections, and explicit dispatch
remain distinct.

## 1. Preservation standard

"No loss" in this note means no loss of semantic expressiveness. A source
compatibility spelling may be deprecated and mechanically rewritten, but a
program that can be expressed today must remain expressible with the same
meaning.

A surface simplification is acceptable only when all of the following hold:

- **Functionality:** the canonical form reaches every currently admitted
  semantic operation. Removed aliases have a mechanical rewrite.
- **Correctness:** desugaring runs before type, effect, ownership, borrow,
  pattern, and proof checking. It cannot bypass or weaken those checks.
- **Performance:** canonical and compatibility forms lower to the same SemIR
  operation. Sugar introduces no allocation, boxing, iterator object,
  dispatch, reference count, hidden copy, or extra evaluation.
- **Representation:** semantic type identity, layout, alignment, ABI, and
  representation selection are unchanged.
- **Evaluation:** operand order, number of evaluations, traps, cleanup, and
  short-circuit behavior are unchanged.
- **Verification:** the same proof obligations and extraction artifacts are
  produced after normalization.
- **Diagnostics:** source ranges remain attached through lowering, and a
  compatibility rewrite cannot silently select a different parse.

Source compatibility is a separate policy choice. If old files must continue
to parse, the compatibility front end can remain while `oak fmt` emits only
the canonical form.

## 2. Evidence from the current tree

The parser exposes several signs that syntax distinctions are costing more
than they provide:

- `parser/parser.go` has separate paths for keyword-form functions and
  declaration-form functions (`parseFunctionStatement` and
  `parseFunctionDefinitionFromName`).
- `positionalArmsAhead` scans as many as 512 significant tokens to decide
  whether `?` begins Boolean positional sugar or pattern arms.
- `bracketGroupPrecedesColon`, `parameterListAhead`, and
  `callableDefinitionAhead` scan as many as 4,096 tokens to distinguish
  declarations from expressions.
- `armDepth` temporarily changes the meaning of `|` while parsing a bare
  match-arm expression and then restores bitwise-or behavior inside bracketed
  constructs.
- the parser accepts both `->` and `=>` for match arms even though the syntax
  specification assigns them different canonical purposes.

The most serious ambiguity is at `parser/parser.go:368-405`. The inferred
binding form examines whether its value begins `IDENT | IDENT`; if so, it
constructs an ADT declaration. Consequently:

```oak
mask := READ | WRITE
```

has the lexical shape of the legacy ADT shorthand rather than an ordinary
inferred binding containing bitwise or. This is a correctness problem, not
only an aesthetic one.

Raw searches over checked-in `*.oak` files give an approximate indication of
where author effort is being spent. These figures include tests, proof
sources, and comments and therefore are not semantic usage counts:

| Shape | Raw occurrences |
| --- | ---: |
| `u32(` | 15,114 |
| `u32(0)` | 3,240 |
| `u32(1)` | 4,038 |
| brace-delimited `while` lines | 1,313 |
| same-name `x = x + u32(1)` increments | 1,345 |
| `view(&` | 250 |
| `span(&` | 530 |
| `fn ` | 159 |
| `|>` | 1, in a comment |
| `operator(` | 0 |

The numbers do not decide a language design. They identify surfaces whose
cost should be justified by actual programs.

## 3. One canonical dialect

The specification, root tour, compatibility tests, type-inference examples,
and older examples currently expose multiple Oak dialects. They disagree on
ADT declarations, constructor qualification, function declarations, match
arrows, blocks, and some binding forms.

The language should distinguish:

- the **canonical source language**, which documentation teaches and
  `oak fmt` prints;
- the **compatibility source language**, which the parser may temporarily
  accept and immediately normalize; and
- the **core language**, which downstream checks and backends consume.

Only the first should be presented as Oak syntax. The compatibility language
is migration machinery, not a set of equally preferred alternatives.

Every Oak fragment in documentation should be extracted and parsed in CI.
Fragments intended to be valid should also be type-checked where their
context permits it. Invalid examples should declare their expected diagnostic
code. This prevents the documentation from creating new dialects accidentally.

### Recommendation

Use explicit introducers for named declaration categories:

- `type` for nominal types and ADTs;
- `interface` for compile-time structural requirements;
- `fn` for named functions and methods;
- `protocol`, `literals`, `tag`, and `theorem` for their respective
  categories.

Keep the compact value grammar:

- `name: Type = value` for an explicitly typed binding;
- `name := value` for a new inferred binding; and
- `name = value` for reassignment.

This gives the parser the declaration category at the beginning of a named
category declaration. It gives up the aesthetic rule that every declaration
looks exactly like `name: type = value`, but preserves the semantic fact that
names are bound to typed entities. The benefit is local parsing and better
error recovery.

## 4. Remove the ADT shorthand immediately

The `Name := A | B` shorthand should not remain in the compatibility grammar
because it conflicts with an ordinary inferred value expression. A
compatibility alias is safe only when it cannot select a different parse.

The migration is mechanical:

```oak
type Color = Red | Green | Blue
```

or, if the declaration-form syntax remains canonical for v1:

```oak
Color: type = Red | Green | Blue
```

The formatter or a dedicated fix command can rewrite legacy declarations.
After this exception is removed, `name := left | right` must always be a value
binding.

## 5. Give functions one declaration grammar

The current function surface has independent alternatives for:

- a leading `fn`, a colon-led declaration, or a colon-less declaration;
- `:` or `->` before the result type;
- `= expression`, `= { block }`, or a bare brace block;
- typed and legacy untyped function literals; and
- method/generic forms that require `fn` even when ordinary functions do not.

These choices compose, so authors and tools must know more combinations than
there are semantic function forms.

### Proposed canonical rule

A named function begins with `fn`. Its parameters always carry the same
parameter grammar. `:` introduces the declared result type. `->` is reserved
for function types. An expression body uses `=`; a statement body is a bare
brace block. There is no `= { ... }` variant and no implicit result type for
an untyped legacy literal.

```oak
fn add(a: i32, b: i32): i32 = a + b

fn mix(a: u8, b: i32, c: i32): i32 {
  b + c
}

handler: (i32, i32) -> i32 = add
```

Methods, generic functions, extern declarations, and kernels should extend
this one head rather than switch to another function grammar.

Compatibility function spellings can normalize to the existing function AST
before name resolution. A canonical formatter then makes the migration
automatic.

## 6. Separate conditionals and pattern matching at the surface

Oak is right to have one semantic branching operation. That does not require
one punctuation-heavy authoring construct.

The current `?` family combines:

- Boolean positional branches;
- one-arm statement conditions with an implicit unit branch;
- full pattern matching;
- leading `|` layout arms;
- `|` as both arm separator and bitwise or; and
- two accepted arm arrows.

The resulting arm rule occupies `docs/spec/10-syntax.md:400-411`: bitwise or
inside a bare arm requires parentheses or a bracketed construct, and a third
pipe has a dedicated diagnostic because it once changed the parse of the
whole expression.

### Proposed surface

Use `if`/`else` for a Boolean and `match` for patterns. Use `=>` as the sole
match-arm arrow and newline, semicolon, or comma as the arm separator; do not
require a leading pipe.

Both forms lower immediately to the current exhaustive match AST. A missing
`else` in statement position lowers to the same explicit false-to-unit arm as
today. Value-position conditionals still require compatible branches.

This preserves:

- single evaluation of the condition or scrutinee;
- exhaustiveness and redundancy checking;
- GADT refinements and evidence binding;
- expression-valued branching;
- statement-bearing branches;
- backend selection of an `if`, conditional expression, switch, or other
  equivalent control flow; and
- the doctrine that domain state should be modeled by an ADT rather than
  Boolean fields.

It removes positional-arm prediction, special `armDepth` parsing, match-arrow
compatibility, and the bare-arm bitwise-or exception.

If new keywords are rejected, the smaller alternative is to keep `?` but
require explicit patterns and `=>` for every arm, including `true` and
`false`. That is less ergonomic for ordinary conditions but still removes the
ambiguous positional form.

## 7. Make braces canonical; treat layout as input compatibility

`docs/SYNTAX_DIRECTION.md` intends layout and explicit braces to denote the
same AST and permits mixed style. In the current implementation, layout
insertion is construct-sensitive, and newline rules help distinguish
statements from continuation. Meanwhile, checked-in loops overwhelmingly use
explicit braces.

The language need not delete layout syntax to simplify authoring. It should
choose one output language:

- `oak fmt` prints explicit braces by default;
- layout input, where accepted, is normalized to those braces;
- documentation uses the formatter output; and
- a layout formatter mode, if retained, must be a complete pretty-printing
  choice rather than a second grammar authors must mix manually.

This preserves layout-based source compatibility without making every syntax
rule describe two equal canonical spellings.

## 8. Add a structural, allocation-free `for`

The existing `while` is an appropriate core operation. Requiring every
counted traversal to spell initialization, comparison, indexing, and
increment is not an advantage for correctness once the compiler can elaborate
the same proof shape itself.

The first `for` increment should support only forms with a transparent
lowering:

```oak
for i in 0..<len(xs) {
  use(xs[i])
}

for x in xs {
  use(x)
}
```

The lowering must be specified, including integer type, half-open bound,
evaluation count for the range endpoints or collection expression, index
progression, overflow reasoning, and borrow extent. The result should be the
same counted loop an author writes today.

The initial element form should be read-only. Mutable element iteration,
strided iteration, iterator protocols, generators, and user-defined iteration
should not be inferred from this proposal; each adds ownership or hidden-work
questions. Authors can continue to use indexed `while` for those cases.

No range object or iterator value exists at run time unless one is explicitly
requested as data.

## 9. Finish contextual literal inference

Oak already permits expected types to determine literals in several
positions. The rule should be made uniform wherever a single expected type is
available:

- typed initializers;
- arguments;
- returns;
- operands whose other side fixes the type;
- indices and lengths with a declared index type;
- aggregate fields and elements; and
- pattern payloads.

The formatter or vet tool can then remove redundant constructors such as
`u32(0)` and `u32(1)` only where type checking proves that the unsuffixed
literal elaborates to exactly the same typed constant. Constructors stay when
they select or change a type.

An unconstrained literal remains an error. Oak should not introduce C-style
default promotions or a global default integer merely to save annotations.

## 10. Collapse numeric conversion names, not conversion semantics

Names built from source type, conversion mode, and destination type produce a
large API family even though the source type is statically known from the
operand. The author should select:

- the conversion mode: checked, truncating, saturating, rounding, or
  bit-preserving; and
- the destination type.

For example, a generic form such as `trunc[u8](x)` can elaborate to the same
intrinsic currently selected by a name such as `u8_trunc_u32`.

The modes must **not** be collapsed into a permissive cast. They have distinct
proof rules, trap behavior, and machine operations. The proposal only factors
the spelling and registry; it does not add implicit conversions.

Arithmetic policy names can be factored in the same way if the resulting
namespace remains discoverable: checked, saturating, wrapping, and trapping
operations stay explicit and lower to their current primitives.

## 11. Consider letting `view` and `span` establish the borrow

`view(&owner)` and `span(&owner)` state the borrow twice: the operation says a
borrowed capability is being created, and `&` marks the same owner as
borrowed. The corpus contains roughly 780 raw occurrences of these two
shapes.

If `view` and `span` accept only addressable owners and valid owner
projections, they can establish the borrow themselves:

```oak
v := view(owner)
s := span(owner)
```

The borrow checker would record the same source owner, mutability, region,
alignment, and escape restrictions. `&` would remain for operations that
actually request a reference or address value.

This needs a focused RFC rather than immediate adoption. It must establish
that `&` does not currently disambiguate overloads, evaluation categories, or
temporary lifetimes, and that a constructor cannot accidentally borrow a
computed temporary.

## 12. Unify compile-time structural constraints

Oak currently has several constructs that describe admissible compile-time
structure:

- semantic record shapes;
- extensible record constraints;
- method interfaces; and
- module sealing signatures.

They overlap because none needs to determine runtime field layout. A single
structural constraint mechanism could require fields, methods, values,
associated types, and nested constraints.

Runtime `struct` remains separate and continues to determine product layout,
field order, padding, alignment, and ABI. A structural interface creates no
object, vtable, box, or witness allocation. Generic specialization can keep
using the same static evidence it uses today.

This consolidation should be judged by whether it removes duplicate
subtyping, substitution, diagnostic, and module-sealing rules—not merely by
whether the declarations look similar.

## 13. Put callable contracts on callable types

The function-type story is currently split among ordinary types, effect rows,
resource parameter modes, result provenance, protocol `via` clauses, and
side-channel facts.

`docs/spec/60-effects-allocation.md:82-109` says effect rows do not take part
in type identity and lists assignment-after-declaration and return values as
flows that are not checked. A function value can therefore cross positions
where the row is trusted rather than re-established. Resource contracts have
a related duplication: a function declaration has parameters and a result,
while a protocol projection may separately describe whether those resources
are borrowed, mutated, consumed, fresh, or aliased.

The semantic type of a callable should carry:

- ordinary parameter and result types;
- parameter modes such as borrow, mutable borrow, and consume;
- result provenance such as fresh, alias of an argument, or borrow from an
  argument; and
- the upper bound of its effect row.

This information may remain erased at runtime. Once it participates in
callable compatibility, function values moving through locals, fields,
arguments, and returns are checked by the same variance and subsumption rules.
A protocol `via` reference can infer the contract from the named callable
instead of restating it.

This is both a simplification and a correctness tightening. It needs a
semantic RFC with explicit variance, joins, inference boundaries, generic
substitution, and ABI-erasure rules.

## 14. Reconcile initialization and defaults

The current documents do not state one initialization rule:

- `docs/spec/10-syntax.md:47-53` says an uninitialized declaration is not yet
  safe core syntax;
- `docs/spec/20-types.md:912-915` describes zero-initialized storage; and
- `docs/spec/30-adts-patterns.md:59-63` says an uninitialized sum contains its
  first variant with a zero payload.

Safe local bindings should always be initialized. Intentional zero
initialization should use one explicit operation whose static precondition
proves that zero is a valid value of the destination type. The backend may
still implement it with BSS placement, zero stores, or a memset.

Static storage may retain omitted initialization as an explicit storage-class
rule. An ADT should not silently select its first variant unless the type
explicitly designates a default constructor and that default is valid.

Field and payload defaults should likewise have one owner. Either construction
applies declared defaults consistently, including update syntax, or every
omitted field is an error. Several partially overlapping default mechanisms
would recreate the same authoring problem.

## 15. Optional pruning and deferral

The following forms have little checked-in use or overlap another mechanism.
They are candidates for removal from the canonical surface, not evidence for
immediate deletion from the compatibility parser.

### Pipeline and leading-dot accessors

Uniform-call/fluent syntax is used by real Oak programs. Pipeline syntax has
one raw occurrence, in a comment, and inserts its data argument in a different
direction from uniform call syntax. Keeping both creates two mental models for
the same data flow.

Prefer ordinary calls plus uniform-call syntax. A first-class accessor can be
an explicitly typed noncapturing function. If pipeline syntax is retained, it
should use the same receiver position as uniform call syntax.

### User-defined infix operators

No `operator(` definition appears in checked-in Oak source. Named functions
can carry the same laws and specialize to the same machine operation. Custom
operators should remain deferred until a pilot demonstrates that named calls
materially obscure an algorithm and that precedence, imports, diagnostics,
and law lookup have a complete design.

### Runtime quantifiers

`forall` and `exists` are valuable in theorem and proof contexts. As runtime
forms they are effectful enumerating loops whose functionality is expressible
by ordinary loops or allocation-free library `all`/`any` functions. Restricting
the syntax to proof contexts would shrink the runtime core without weakening
the proof language.

### Scoped reduction-order blocks

`order tree`, `order left`, and bounded-order blocks contextually rewrite
reduction calls. Explicit `reduce.tree`, `reduce.left`, and
`reduce.bounded` operations make the selected order visible at the operation
and retain laws on the combine function. If scoped order remains important for
large generated regions, it should normalize to those explicit calls before
checking.

### `defer`

`defer` has little corpus use but should not be removed merely for that
reason. Terminal resource cleanup and early exits can make it essential. Its
evaluation-time and capture semantics deserve a separate review; it is not a
priority authoring simplification.

## 16. Distinctions to retain

The following are not redundant syntax even when their spellings can improve:

- `[N]T`, `[]T`, and `[*]T`: ownership, read capability, write capability,
  extent, and provenance differ;
- immutable borrow, mutable borrow, and consumption;
- checked, truncating, saturating, rounding, wrapping, and bit-preserving
  operations;
- semantic type identity versus runtime representation;
- transparent, packed, aligned, and no-padding layout requirements;
- effect families, scopes, and prohibitions;
- explicit representation and dispatch selection;
- protocols, typestates, guards, and transition evidence;
- laws and proof obligations;
- literal sets and their projected implementations;
- `try` and deliberate result discard; and
- safe versus unsafe machine operations.

These distinctions carry facts used by the checker, proofs, ABI, or generated
machine code. Merging them would make Oak smaller only by weakening it.

## 17. Proposed delivery order

### Phase 0 — measure and freeze

1. Define the canonical source grammar in `10-syntax.md`.
2. Inventory every compatibility spelling and its exact canonical rewrite.
3. Extract and validate documentation snippets in CI.
4. Record parser ambiguity tests and current SemIR/backend goldens before
   changing normalization.

### Phase 1 — correctness and canonicalization

1. Remove the `Name := A | B` routing ambiguity.
2. Add formatter/fix rewrites for legacy ADT and function forms.
3. Make the specification, tour, examples, tests, and standard library use
   only canonical output.
4. Keep compatibility parsing only for aliases with an unambiguous rewrite.

### Phase 2 — branching and functions

1. Introduce the canonical conditional and match surfaces.
2. Normalize both to the existing match AST before checking.
3. Normalize every function spelling to one function declaration AST.
4. Deprecate positional arms, alternate match arrows, alternate result
   punctuation, and duplicate block-body markers.

### Phase 3 — high-volume authoring reductions

1. Complete bidirectional literal inference and add safe formatter fixes.
2. Introduce parameterized explicit numeric conversions.
3. Add the bounded/counting `for` lowering and read-only element traversal.
4. Evaluate the `view(owner)` and `span(owner)` borrow spelling separately.

### Phase 4 — semantic consolidation

1. Specify structural interfaces across records, methods, and module sealing.
2. Make callable effects, modes, and provenance part of callable semantic
   compatibility.
3. Reconcile local, static, aggregate, and ADT initialization.
4. Remove or defer unused pipeline, operator, runtime-quantifier, and scoped
   order syntax only after compatibility and pilot review.

## 18. Equivalence gates

Each migration increment should test a compatibility source and its canonical
rewrite as a pair. After parsing and desugaring, the pair must have:

1. the same canonical AST, ignoring source positions;
2. the same resolved names and semantic type identities;
3. the same ownership, lifetime, effect, provenance, and representation facts;
4. the same exhaustiveness and proof obligations;
5. the same SemIR and extracted formal artifact;
6. equivalent C, native, and Metal output after normal backend normalization;
7. the same evaluation count, order, traps, cleanup, and observable behavior;
8. unchanged benchmark results within the existing noise policy; and
9. diagnostics mapped back to the spelling the author actually wrote.

A compatibility spelling that cannot meet these gates is not an alias and
should be rejected rather than guessed.

## 19. Decisions needed

The proposals divide into three confidence levels.

**Adopt as direction now:**

- one canonical dialect and formatter output;
- removal of the ambiguous ADT shorthand;
- documentation-snippet validation;
- one function grammar; and
- safe removal of redundant numeric literal constructors.

**Write focused RFCs:**

- `if`/`match` surface normalization;
- allocation-free `for` lowering;
- parameterized conversions;
- borrow-establishing `view`/`span`;
- structural-interface unification;
- callable contract identity; and
- initialization/default semantics.

**Measure and potentially prune:**

- pipeline and leading-dot accessors;
- user-defined infix operators;
- runtime quantifiers; and
- scoped reduction-order blocks.

The central design choice is whether Oak values a uniform
`name: type = value` visual algebra more than it values locally decidable
syntax. The current parser complexity and the ADT/bitwise ambiguity indicate
that explicit declaration introducers are the safer trade. Oak can retain its
five semantic axes and strict cost model while presenting substantially fewer
ways to spell them.
