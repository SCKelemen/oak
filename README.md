# Oak

Oak is an experimental systems language focused on explicit semantics, predictable machine representation, and a compiler architecture that can eventually project one semantic definition into executable code, verification artifacts, tests, schemas, debugger metadata, and documentation.

The active language implementation lives on the `specification` line of development.

## Current compiler direction

The host compiler targets Go 1.27 and is moving toward a Roslyn-style, value-oriented API:

```go
compiler.New().
    WithSource("main.oak", source).
    SemanticModel()
```

The canonical front end is:

```text
source
  -> scanner
  -> layout normalization
  -> parser
  -> syntax tree
  -> semantic model
  -> lowering / projections
```

Oak accepts explicit C-style statement blocks and is adding equivalent indentation-delimited ML-style blocks. Both forms normalize to the same parser semantics rather than selecting different grammar modes.

The long-term architectural rule is:

> Define a semantic fact once; project it many ways.

See:

- [`docs/SYNTAX_DIRECTION.md`](docs/SYNTAX_DIRECTION.md) for optional-brace/layout syntax;
- [`docs/SEMANTIC_ARCHITECTURE.md`](docs/SEMANTIC_ARCHITECTURE.md) for the Semantic IR and proof/model/code projections;
- [`docs/COMPILER_API.md`](docs/COMPILER_API.md) for the Go 1.27 fluent compiler and parser architecture.

## Status

Oak is experimental. Several language subsystems and historical specifications coexist in this repository while the compiler is consolidated around the semantic architecture above. The normal Go test suite is the current executable correctness gate. The golden-file corpus is being repaired because some historical expected fixtures are missing or predate current token/AST metadata.
