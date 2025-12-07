# Serialization Package

This package provides JSONL (JSON Lines) serialization for each stage of the Oak compilation pipeline, enabling regression testing at every step.

## Pipeline Stages

The compilation pipeline consists of the following stages, each serializable to JSONL:

1. **Source Code** (bytes) → **Tokens** (lexemes)
2. **Tokens** → **AST** (via parser)
3. **AST** → **Lowered AST** (via lowering)
4. **Lowered AST** → **Codegen** (C code output)

## Usage

### Serializing the Full Pipeline

```go
import "github.com/SCKelemen/oak/serialize"

sourceCode := `
x: i32 = 5
y: i32 = 10
z: i32 = x + y
`

objEnv := object.NewEnvironment()
tc := typechecker.New(objEnv)

outputs, err := serialize.SerializePipeline(sourceCode, "output_dir", tc)
if err != nil {
    log.Fatal(err)
}

// outputs contains paths to:
// - outputs.Tokens: tokens.jsonl
// - outputs.AST: ast.jsonl
// - outputs.LoweredAST: lowered_ast.jsonl
// - outputs.Codegen: codegen.jsonl
```

### Serializing Individual Stages

```go
// Serialize tokens
tokens := []token.Token{...}
err := serialize.SerializeTokens(tokens, "tokens.jsonl")

// Serialize AST
program := &ast.Program{...}
err := serialize.SerializeAST(program, "ast.jsonl")

// Serialize codegen output
cCode := "..."
err := serialize.SerializeCodegen(cCode, "codegen.jsonl")
```

## JSONL Format

Each stage produces a JSONL file where each line is a JSON object:

### Tokens (`tokens.jsonl`)
```json
{"kind":"IDENT","literal":"x","line":2,"column":1,"byte_start":1,"byte_end":2}
{"kind":"COLON","literal":":","line":2,"column":2,"byte_start":2,"byte_end":3}
{"kind":"IDENT","literal":"i32","line":2,"column":4,"byte_start":4,"byte_end":7}
```

### AST (`ast.jsonl`)
```json
{"type":"Program","data":{"statement_count":3}}
{"type":"VariableDeclaration","data":{"name":"x","type":"i32","value":{...}}}
```

### Codegen (`codegen.jsonl`)
```json
{"line_number":1,"content":"#include <stdint.h>"}
{"line_number":2,"content":"int32_t x = 5;"}
```

## Regression Testing

### Comparing JSONL Files

```go
equal, line1, line2, desc, err := serialize.CompareJSONLFiles("expected.jsonl", "actual.jsonl")
if !equal {
    t.Errorf("Files differ at line %d/%d: %s", line1, line2, desc)
}
```

### Reading JSONL Files

```go
objects, err := serialize.ReadJSONLFile("tokens.jsonl")
// objects is []interface{} containing all JSON objects
```

### Getting a Diff

```go
diff, err := serialize.DiffJSONLFiles("expected.jsonl", "actual.jsonl")
fmt.Println(diff) // Human-readable diff
```

## Test Structure

For regression tests, you can:

1. **Generate expected outputs** from known-good source code:
   ```go
   serialize.SerializePipeline(sourceCode, "testdata/expected/", tc)
   ```

2. **Compare against expected** in tests:
   ```go
   serialize.SerializePipeline(sourceCode, "testdata/actual/", tc)
   equal, _, _, desc, _ := serialize.CompareJSONLFiles(
       "testdata/expected/tokens.jsonl",
       "testdata/actual/tokens.jsonl",
   )
   ```

3. **Update expected outputs** when making intentional changes:
   ```bash
   cp testdata/actual/*.jsonl testdata/expected/
   ```

## Benefits

- **Granular testing**: Test each compilation stage independently
- **Easy debugging**: See exactly where the pipeline diverges
- **Version control friendly**: JSONL files are text-based and diffable
- **Regression detection**: Catch unintended changes at any stage
- **Incremental development**: Test parser changes without running full pipeline
