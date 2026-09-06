# Compiler API

Oak's host compiler targets Go 1.27 and uses generic methods to expose a typed, fluent compilation pipeline.

Go 1.27 permits concrete methods to declare their own type parameters. Oak uses that capability for compiler-stage transformations, not as a reason to make every compiler data structure generic.

## Goals

- one obvious public path through scanner, parser, semantic analysis, lowering, and code generation;
- Roslyn-style value-oriented APIs (`Compilation`, `SyntaxTree`, `SemanticModel`);
- typed stage transitions without package-level `MapXToY` helper proliferation;
- errors short-circuit automatically;
- compiler configuration is explicit and derived with `With...` methods;
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

## Relationship to layout syntax

The intended parse entry point is:

```text
SourceText
    -> scanner.Scanner
    -> layout.Normalizer
    -> parser.Parser
    -> SyntaxTree
```

At present `parser.Parser` is still coupled to `*scanner.Scanner`, so `Compilation.Parse` uses the existing direct scanner path. The next parser integration change should make the parser depend on a small `NextToken() token.Token` source interface and then place `layout.Normalizer` in this single public parse path.

That is important: callers should not choose whether layout normalization happens. Explicit-brace and indentation syntax are two source forms of the same language and must enter the same parser semantics.

## Why generic methods matter

Before Go 1.27, changing a pipeline result type generally required package-level generic functions such as:

```go
MapStage[T, U](stage Stage[T], fn func(T) U) Stage[U]
```

Go 1.27 lets the operation live where users expect it:

```go
stage.Map(fn).Then(next)
```

This makes the API much closer to the fluent style Oak originally wanted without sacrificing static typing.

## Limits

Generic methods cannot be interface methods in Go 1.27. Oak therefore keeps the generic transformation surface on concrete compiler values such as `Stage[T]`. Small non-generic interfaces should still be used for capabilities such as token sources where dynamic substitution is useful.

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

The API should preserve Oak's core rule: define a semantic fact once and let every compiler phase that can use it consume the same fact.
