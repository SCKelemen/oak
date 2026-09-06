# Legacy Specification Reconciliation

The top-level Oak documents below are retained as design history and examples until their useful content has been fully migrated. They are **not authoritative** when they disagree with `docs/spec/`.

| Legacy document | Normative destination | Reconciliation notes |
| --- | --- | --- |
| `SPEC.md` | entire `docs/spec/` tree | foundational design source; several syntax/semantic choices were later contradicted by newer docs |
| `ADT_AND_PATTERN_MATCHING.md` | `10-syntax.md`, `30-adts-patterns.md` | preserves ADTs/patterns; canonicalizes `=>`, `Type.Case`, `.Case`; separates payload defaults from representation/metadata |
| `tags_and_phantoms.md` | `30-adts-patterns.md`, `80-metadata.md` | valuable split between phantom identity and metadata; old default/tag syntax no longer normative |
| `TAGGING_AND_LABELING.md` | `80-metadata.md` | semantic concept retained; backtick surface syntax remains unresolved/legacy |
| `type_universe.md` | `20-types.md` | core bottom/top/join/meet ideas retained; ADTs separated from arbitrary unions; record composition separated from subtyping; implementation laws must be fixed to match the spec |
| `INTRUSIVE_STRUCTURES.md` | `20-types.md`, `40-records.md`, acceptance tests | intrusive structures remain an important zero-cost language benchmark; record `&` is composition, interface `&` is constraint conjunction |
| `borrow_checker.md` | `50-borrowing.md` | many-readers/one-writer and views/spans retained; negative-index policy moved out of borrow semantics; future regions integrated with allocation/effect model |
| `STRINGS_ENCODING_SPEC.md` | `70-strings.md` | encoding tags and zero-overhead views retained; arbitrary bytes may not become valid text without validation |
| `STRINGS_INTEGRATION.md` | `50-borrowing.md`, `70-strings.md` | borrow-preserving wrappers retained; unsafe reinterpretation language tightened |
| `STRINGS_UTF16_UTF32_SPEC.md` | `70-strings.md` | code-unit-parametric text retained; exact `rune` semantics need one canonical refined `u32` decision |
| `C_BACKEND_SPEC.md` | `90-backend.md` | readable C remains bootstrap/reference backend; C no longer defines Oak semantics |
| `json_lexer.md` | acceptance/workload tests + `90-backend.md` | retained as a language benchmark for zero-allocation parsing/state machines, not a core language spec |
| `VARIABLE_SYNTAX.md` | `10-syntax.md` | `x:T=e`, `x:=e`, `x=e` retained; implicit NULL/uninitialized safe variables rejected pending definite-init semantics |
| `TOUR_OF_OAK.md` | future generated/curated language tour | examples contain multiple historical syntaxes; should be regenerated only from normative syntax after consolidation |
| `REPL_FEATURES.md` | implementation docs/tests | useful historical behavior examples; not normative grammar/semantics |
| `FEATURES_COMPLETE.md` | `STATUS.md` | historical completion claim replaced by evidence-based S/I/T/M/P/R matrix |
| `IMPLEMENTATION_STATUS.md` | `STATUS.md` | historical implementation snapshot only |
| `IMPLEMENTATION_SUMMARY.md` | `STATUS.md` | historical implementation snapshot; contains known stale statements such as future C backend work |

## Major conflicts resolved so far

### Match arrows

Legacy docs accept both `->` and `=>` for match arms.

Normative decision:

```text
-> function type
=> match arm
```

### Constructor qualification

Legacy docs contain `.Case`, `Type.Case`, and `Type::Case`.

Normative decision:

```text
Type.Case canonical qualified form
.Case context-inferred shorthand
Type::Case legacy only
```

### Function return syntax

Legacy docs contain both:

```text
fn f(...): T
fn f(...) -> T
```

Normative decision:

```text
:  declaration/type annotation
-> function type
```

so function declarations use `: T`.

### ADT literal/default/tag semantics

Legacy documents variously interpret a value attached to an ADT arm as:

- a payload default;
- a raw/literal view;
- an enum-like numeric value;
- protocol metadata.

Normative decision: these are separate axes.

```text
payload default      -> ADT construction semantics
runtime discriminant -> representation
wire/protocol code   -> typed metadata/representation projection
human/docs labels    -> metadata
```

### Union/intersection terminology

Legacy type-universe prose treats `A|B` and `A&B` as general lattice join/meet types while other docs use the same punctuation for ADT constructor lists, record composition, and interface conjunction.

Normative decision:

- semantic checker may internally use joins/meets;
- ADT `|` enumerates constructors of one nominal sum;
- record `&` is definition-time composition, not subtyping;
- constraint `&` means predicate conjunction;
- arbitrary runtime union/intersection values are not implied.

### Record order

Legacy type-universe text suggested canonical sorting of record fields.

Normative decision: **source declaration order is preserved**. A canonical internal lookup order may exist separately, but it cannot replace source order for layout/schema/tooling projections.

### `any`

Legacy pattern docs use runtime typecase over `any`, while the type-universe document also describes `any` as an optional top.

Normative decision: static `any` as a top in type reasoning does not imply a dynamic boxed runtime value. Runtime `any`/typecase remains out of core until its representation/effects are explicitly specified.

### Strings

Legacy documents sometimes equate `string` with raw `[]u8`.

Normative decision: `string` is validated UTF-8 text with a view-like representation. Equal representation does not erase the validity invariant.

### Uninitialized variables

Legacy `VARIABLE_SYNTAX.md` says uninitialized declarations become `NULL`.

Normative decision: safe Oak has no implicit null initialization. Definite initialization must be proved if uninitialized declarations are ever admitted.

## Remaining unresolved design decisions

These require focused feature RFC/spec work rather than accidental parser behavior:

- exact final typed-attribute syntax;
- whether ADT constructor defaults can be overridden explicitly;
- exact GADT refinement surface syntax;
- whether negative indices remain part of sequence indexing;
- exact safe integer overflow/division/shift semantics;
- final `rune` spelling/refinement;
- dynamic existential/interface values, if any;
- runtime `any`, if any;
- closures that escape and how allocator choice is expressed;
- stable FFI/wire representation syntax;
- protocol/typestate surface syntax.

## Cleanup policy

Once all useful content from a legacy document has been migrated and its remaining statements are either obsolete or duplicated, replace it with a short pointer to the normative spec or remove it in a dedicated cleanup commit.

Do not mass-delete the historical corpus before reconciliation; it still contains useful examples and design intent.