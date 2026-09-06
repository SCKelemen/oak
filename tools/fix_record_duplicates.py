from pathlib import Path


def replace_once(path: str, old: str, new: str) -> None:
    p = Path(path)
    text = p.read_text()
    if old not in text:
        raise SystemExit(f"expected pattern not found in {path}: {old[:80]!r}")
    p.write_text(text.replace(old, new, 1))


replace_once(
    "ast/ast.go",
    """func (rl *RecordLiteral) AddField(tok token.Token, name string, value Expression) {\n\tif rl.Fields == nil {\n\t\trl.Fields = make(map[string]Expression)\n\t}\n\trl.Fields[name] = value\n\trl.FieldOrder = append(rl.FieldOrder, RecordField{Token: tok, Name: name, Value: value})\n}\n""",
    """func (rl *RecordLiteral) AddField(tok token.Token, name string, value Expression) bool {\n\tif rl.Fields == nil {\n\t\trl.Fields = make(map[string]Expression)\n\t}\n\tif _, exists := rl.Fields[name]; exists {\n\t\treturn false\n\t}\n\trl.Fields[name] = value\n\trl.FieldOrder = append(rl.FieldOrder, RecordField{Token: tok, Name: name, Value: value})\n\treturn true\n}\n""",
)

replace_once(
    "parser/parser.go",
    "\t\trecord.AddField(fieldToken, fieldName, fieldType)\n",
    """\t\tif !record.AddField(fieldToken, fieldName, fieldType) {\n\t\t\tp.addErrorAtCurrentToken(fmt.Sprintf(\"duplicate record field %q\", fieldName))\n\t\t\treturn nil\n\t\t}\n""",
)

replace_once(
    "parser/parser.go",
    "\t\trecord.AddField(fieldToken, fieldName, fieldValue)\n",
    """\t\tif !record.AddField(fieldToken, fieldName, fieldValue) {\n\t\t\tp.addErrorAtCurrentToken(fmt.Sprintf(\"duplicate record field %q\", fieldName))\n\t\t\treturn nil\n\t\t}\n""",
)

Path("parser/record_duplicates_test.go").write_text(
    r'''package parser

import (
    "strings"
    "testing"

    "github.com/SCKelemen/oak/scanner"
)

func hasDuplicateFieldError(errors []string) bool {
    for _, err := range errors {
        if strings.Contains(err, "duplicate record field") {
            return true
        }
    }
    return false
}

func TestRecordLiteralRejectsDuplicateFields(t *testing.T) {
    p := New(scanner.New("{ x: 1, x: 2 }"))
    _ = p.ParseProgram()
    if !hasDuplicateFieldError(p.Errors()) {
        t.Fatalf("expected duplicate record literal field diagnostic, got %v", p.Errors())
    }
}

func TestRecordTypeRejectsDuplicateFields(t *testing.T) {
    p := New(scanner.New("Point: type = { x: i32, x: u32 }"))
    _ = p.ParseProgram()
    if !hasDuplicateFieldError(p.Errors()) {
        t.Fatalf("expected duplicate record type field diagnostic, got %v", p.Errors())
    }
}
'''
)
