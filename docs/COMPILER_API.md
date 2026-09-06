# Compiler API

Oak's host compiler targets Go 1.27 and uses generic methods to expose a typed, fluent compilation pipeline.

Go 1.27 permits concrete methods to declare their own type parameters. Oak uses that capability for compiler-stage transformations and repeated parser mechanics, not as a reason to make every compiler data structure generic.

## Goals

- one obvious public path through scanner, layout normalization, parser, semantic analysis, lowering, and code generation;
- Roslyn-style value-oriented APIs (`Compilation`, `SyntaxTree`, `SemanticModel`);
- typed stage transitions without package-level `MapXToY` helper proliferation;
- errors short-circuit automatically;
- compiler configuration is explicit and derived with `With...` methods;
- explicit-brace and indentation syntax normalize to the same parser semantics;
- later semantic projections (Lean, temporal models, schemas, debugger metadata) can hang from the same `Compilation` / Semantic IR surface.

## Current API

```go
c := compiler.New().
    WithSource("main.oak", source).
    WithPackageName("main").
    WithPlatformSizes(64, 64)

syntax, err := c.SyntaxTree().Get()
model, err := c.SemanticModel().Get()
cSource, err := c.EmitC().Get()
```

`Compilation` is a value. `With...` methods return modified copies rather than mutating a shared compiler object.

The command-line compiler now uses this API rather than manually constructing scanner, parser, type checker, lowering, and code-generation phases.

## Generic stages

The core host-side abstraction is:

```go
type Stage[T any] struct { ... }

func (s Stage[T]) Then[U any](fn func(T) (U, error)) Stage[U]
func (s Stage[T]) Map[U any](fn func(T) U) Stage[U]
```

This is intentionally small. It exists to make real compiler transitions compose naturally:

```text
SourceText
   -> SyntaxTree
   -> SemanticModel
   -> LoweredProgram
   -> C / Semantic IR / proof projection
```

The stage abstraction must not hide compiler work, retries, concurrency, or allocation policy. It is typed control flow, not a framework.

## Canonical token pipeline

The compiler-wide streaming contract is deliberately tiny:

```go
type token.Source interface {
    NextToken() token.Token
}
```

Both `scanner.Scanner` and `layout.Normalizer` satisfy it. The canonical front end is:

```text
SourceText
    -> scanner.Scanner
    -> layout.Normalizer
    -> parser.Parser
    -> SyntaxTree
```

`Compilation.Parse` always takes this path. Callers do not opt in to layout normalization. Explicit braces pass through unchanged; indentation-delimited bodies synthesize braces carrying `Synthetic = true` and enter the same parser.

Tests require layout and explicit forms of the same function to produce equivalent AST semantics, and layout-style functions must pass semantic analysis.

### Parser source ownership

`parser.Parser` now stores `token.Source` directly. Its token cursor reads only through that interface, so the parser no longer imports or depends on the concrete scanner implementation.

This removes the old `scanner.FromSource` compatibility layer entirely:

```text
scanner.Scanner ─┐
                 ├─ token.Source -> Parser
layout.Normalizer┘
```

`parser.New` accepts any `token.Source`. `parser.NewSource` remains only as a compatibility spelling for callers that already adopted it; it delegates directly to `New` and does not wrap the source.

The important architectural boundary is therefore real rather than aspirational: token production and token consumption are independently substitutable, while the normal compiler path still requires layout normalization before parsing.

## Generic parser mechanics

Go 1.27 generic methods are useful for repeated structural grammar operations. Oak has a generic separated-sequence primitive on `Parser`:

```go
func (p *Parser) parseSeparated[T any](
    close token.TokenKind,
    separator token.TokenKind,
    allowTrailing bool,
    parseItem func() (T, bool),
) ([]T, bool)
```

It captures the two-token cursor rules shared by comma-separated grammar forms. The first migrations now use it for:

- function-literal argument names;
- function and method parameters;
- generic/type parameter declarations.

Those productions had matching cursor contracts: they start with `currentToken` on the opening delimiter, parse each item with `currentToken` on its first token, and finish with `currentToken` on the closing delimiter.

Other constructs should move only when their positioning contract matches. Invocation arguments and array literals currently have different close-token behavior, so they should be normalized deliberately rather than forced through the helper. We should not rewrite grammar semantics merely to use generics.

## Lexer policy

The lexical state machine should remain explicit. A switch over punctuation/operators is easier to audit than a generic lexer framework and is already close to optimal for Oak.

Generics belong around the lexer where they remove repeated infrastructure: token streams, typed cursors, transformations, collections, and compiler-stage APIs. They should not obscure recognition rules.

## Verification status

The Go 1.27 normal test gate runs `go test -v -race ./...` and is green with the fluent API, token-source composition, layout parsing, direct parser source ownership, and the first separated-list migrations.

The repository's separate golden-file workflow remains red because its fixture set is incomplete/out of date: several named suites have no checked-in expected files, while older lexer/AST snapshots predate recent token/schema changes. This is tracked as golden-fixture debt, not treated as a passing verification gate. New front-end behavior is therefore covered by ordinary parser/compiler tests until the golden corpus is regenerated and made complete.

We should repair that workflow rather than weaken it: regenerate the full expected corpus, review the semantic diffs, commit it atomically, and then require the golden gate again.

## Why generic methods matter

Before Go 1.27, changing a pipeline result type generally required package-level generic functions such as:

```go
MapStage[T, U](stage Stage[T], fn func(T) U) Stage[U]
```

Go 1.27 lets the operation live where users expect it:

```go
stage.Map(fn).Then(next)
```

The same principle applies to parsing: a generic operation that depends on parser state belongs on the concrete `Parser`, not as a package-level helper with a parser argument.

## Limits

Generic methods cannot be interface methods in Go 1.27. Oak therefore keeps generic transformation surfaces on concrete values such as `Stage[T]` and `Parser`. Small non-generic interfaces remain appropriate for capabilities such as `token.Source`, where dynamic substitution is useful.

## Direction

As the Semantic IR lands, `Compilation` should become the root for projections such as:

```text
Compilation
   -> SyntaxTree
   -> SemanticModel
   -> Semantic IR
       -> C / native executable lowering
       -> Lean
       -> temporal/model-checking representation
       -> property/DST generators
       -> wire/schema metadata
       -> debugger/source metadata
       -> documentation
```

Likewise, front-end cleanup should stay incremental:

```text
token.Source-owned Parser
    -> normalize remaining cursor contracts
    -> migrate matching separated/delimited parsing
    -> typed SyntaxList[T] where source fidelity benefits
    -> generic syntax traversal for tools
    -> remaining callers move to Compilation
```
