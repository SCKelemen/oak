# Golden Files

The `golden/` directory contains reference outputs from each stage of the Oak compilation pipeline. These files are used for regression testing to ensure that changes to the compiler don't break expected behavior.

## File Naming Convention

Files follow the pattern: `{name}_{stage_num}_{stage}.{ext}`

- `{name}` - Descriptive name for the test case (e.g., `simple_add`, `type_error`)
- `{stage_num}` - Stage number (typically `0` for the main compilation)
- `{stage}` - Stage identifier (see below)
- `{ext}` - File extension based on content type

## File Types

### Source Files
- **`.oak`** - Oak source code

### Tree Structures (JSON)
- **`.json`** - Tree structures like AST (single JSON object)

### Stream Data (JSONL)
- **`.jsonl`** - Stream-oriented data where each line is a JSON object:
  - Tokens (lexer output)
  - Parser diagnostics/errors
  - Typechecker type environment and errors
  - Borrow checker errors

### Generated Code
- **`.c`** - Generated C code

## Stage Files

For a test case named `example` with stage number `0`:

1. **`example_0_source.oak`** - Original Oak source code
2. **`example_0_lexer.jsonl`** - Token stream from the lexer
3. **`example_0_parser.jsonl`** - Parser output (success marker or errors)
4. **`example_0_ast.json`** - Abstract Syntax Tree (JSON format)
5. **`example_0_typechecker.jsonl`** - Typechecker output (type environment, errors)
6. **`example_0_lowering.json`** - Lowered AST after desugaring
7. **`example_0_borrowchecker.jsonl`** - Borrow checker output (errors or success)
8. **`example_0_codegen.c`** - Generated C code

## Error Handling

All stages serialize errors when they occur, making this suitable for **negative tests** as well:

- **Parser errors**: Serialized to `parser.jsonl` with error messages
- **Typechecker errors**: Serialized to `typechecker.jsonl` with error messages and diagnostics
- **Borrow checker errors**: Serialized to `borrowchecker.jsonl` with error messages

When errors occur:
- The stage's output file still contains the errors (not empty)
- Subsequent stages may be skipped or contain error placeholders
- Codegen will include a comment explaining why generation was skipped

## Usage

### Generating Golden Files

```go
import "github.com/SCKelemen/oak/serialize"

sourceCode := `x: i32 = 5`
objEnv := object.NewEnvironment()
tc := typechecker.New(objEnv)

outputs, err := serialize.SerializeToGolden("test_name", 0, sourceCode, tc)
// Creates all golden files in golden/ directory
```

### Loading Golden Files

```go
outputs, err := serialize.LoadGolden("test_name", 0)
// Returns paths to all golden files for comparison
```

### Comparing Outputs

```go
// Compare JSONL files
equal, line1, line2, desc, err := serialize.CompareJSONLFiles(
    "golden/expected_0_typechecker.jsonl",
    "golden/actual_0_typechecker.jsonl",
)

// Get human-readable diff
diff, err := serialize.DiffJSONLFiles(
    "golden/expected_0_typechecker.jsonl",
    "golden/actual_0_typechecker.jsonl",
)
```

## Regression Testing

Golden files enable regression testing at each pipeline stage:

1. **Lexer**: Verify tokenization hasn't changed
2. **Parser**: Verify AST structure and error messages
3. **Typechecker**: Verify type inference and error detection
4. **Borrow Checker**: Verify borrow rules and error detection
5. **Codegen**: Verify generated C code

When making intentional changes:
1. Update the golden files: `cp golden/actual_* golden/expected_*`
2. Commit the updated golden files
3. Future tests will compare against the new expected outputs
