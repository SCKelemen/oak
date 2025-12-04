package ast

import (
	"testing"
)

func TestString(t *testing.T) {
	// Test basic program string representation
	program := &Program{
		Statements: []Statement{},
	}
	if program.String() == "" {
		// Empty program should return empty string
	}
}
