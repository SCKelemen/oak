package ast

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/token"
)

// A declaration without a body — a dispatching function, or one paired
// with an assembly unit — prints its signature and does not dereference
// the body it lacks.
func TestFunctionStatementStringWithoutBody(t *testing.T) {
	fs := &FunctionStatement{
		Name:     &Identifier{Token: token.Token{Literal: "crc32c"}, Value: "crc32c"},
		Dispatch: []*DispatchSlot{{Feature: "crc", Realization: "crc32c_hw"}},
	}
	got := fs.String()
	if !strings.HasPrefix(got, "fn crc32c(") || !strings.Contains(got, "dispatch { crc: crc32c_hw }") || strings.HasSuffix(got, " ") {
		t.Fatalf("body-less declaration prints as %q", got)
	}
}
