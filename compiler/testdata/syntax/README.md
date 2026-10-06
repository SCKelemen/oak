# Accepted Oak syntax corpus

This directory is the executable contract for source spellings accepted by the public compiler API.

- `*.parse.oak` must pass `Compilation.Parse()`.
- `*.check.oak` must pass `Compilation.Check()`.
- `*.exitN.oak` must pass the full public pipeline, compile/link as C99 with the system `cc`, execute natively, and exit with `N`.

Every case is classified in `compiler/syntax_contract_test.go` as either **canonical** (specified surface) or **compatibility** (accepted migration surface). Compatibility cases require an explicit migration note. Any case that stops before native execution must state why; parse/check evidence is never silently treated as equivalent to runtime E2E.

`compiler/syntax_productions_test.go` also reflects over `parser/parser.go`: every registered prefix and infix expression production must have a corpus witness, and stale witnesses fail after parser changes.
