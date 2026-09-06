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

Both `scanner.Scanner` and `layout.Normalizer` satisfy it. The canonical front end is now:

```text
SourceText
    -> scanner.Scanner
    -> layout.Normalizer
    -> parser.Parser
    -> SyntaxTree
```

`Compilation.Parse` always takes this path. Callers do not opt in to layout normalization. Explicit braces pass through unchanged; indentation-delimited bodies synthesize braces carrying `Synthetic = true` and enter the same parser.

Tests require layout and explicit forms of the same function to produce equivalent AST semantics, and layout-style functions must pass semantic analysis.

### Transitional parser adapter

`parser.Parser` historically stores `*scanner.Scanner` internally. Replacing that field in the monolithic parser should be done as a focused mechanical migration rather than mixed with grammar changes.

Until then:

- `token.Source` is the real boundary;
- `parser.NewSource` is the public source-oriented constructor;
- `scanner.FromSource` is a narrow compatibility adapter for the old concrete field;
- new compiler paths must not bypass `layout.Normalizer`.

Once `Parser` stores `token.Source` directly, the adapter can be deleted without changing callers.

## Generic parser mechanics

Go 1.27 generic methods are useful for repeated structural grammar operations. Oak now has a generic separated-sequence primitive on `Parser`:

```go
func (p *Parser) parseSeparated[T any](
    close token.TokenKind,
    separator token.TokenKind,
    allowTrailing bool,
    parseItem func() (T, bool),
) ([]T, bool)
```

It captures the token-positioning rules shared by constructs such as:

- function parameters;
- invocation arguments;
- generic/type arguments;
- type parameters;
- array elements;
- similar comma-separated grammar forms.

The existing parser methods should migrate onto this primitive incrementally, with parser tests after each conversion. We should not rewrite the grammar merely to use generics.

## Lexer policy

The lexical state machine should remain explicit. A switch over punctuation/operators is easier to audit than a generic lexer framework and is already close to optimal for Oak.

Generics belong around the lexer where they remove repeated infrastructure: token streams, typed cursors, transformations, collections, and compiler-stage APIs. They should not obscure recognition rules.

## Verification status

The Go 1.27 normal test gate runs `go test -v -race ./...` and is green with the fluent API, token-source composition, layout parsing, and generic parser-helper tests.

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
token.Source
    -> Parser stores token.Source directly
    -> generic separated/delimited parsing
    -> typed SyntaxList[T] where source fidelity benefits
    -> generic syntax traversal for tools
    -> remaining callers move to Compilation
```

The next safe parser refactor is intentionally mechanical: replace the stored `*scanner.Scanner` field with `token.Source` without changing parsing behavior, then migrate one comma-separated grammar production at a time onto `parseSeparated[T]` with its existing tests held constant.

The API should preserve Oak's core rule: define a semantic fact once and let every compiler phase that can use it consume the same fact.
