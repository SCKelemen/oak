package parser

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
