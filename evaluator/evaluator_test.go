package evaluator

import (
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func TestEvalIntegerExpr(t *testing.T) {
	tests := []struct {
		input  string
		expecc int64
	}{
		{"5", 5},
		{"10", 10},
	}

	for _, tt := range tests {

		val := testEval(tt.input)
		testIntegerObj(t, val, tt.expecc)
	}
}

func testEval(input string) object.Object {
	lxr := scanner.New(input)
	p := parser.New(lxr)
	program := p.ParseProgram()

	return Eval(program)
}

func TestEvalBooleanExpr(t *testing.T) {
	tests := []struct {
		input  string
		expecc bool
	}{
		{"true", true},
		{"false", false},
	}

	for _, tt := range tests {

		val := testEval(tt.input)
		testBoolObj(t, val, tt.expecc)
	}
}

func testIntegerObj(t *testing.T, obj object.Object, expecc int64) bool {
	result, ok := obj.(*object.Integer)
	if !ok {
		t.Errorf("object is not an Integer, received %T (%+v)", obj, obj)
		return false
	}

	if result.Value != expecc {
		t.Errorf("object.Value has unexpected value; Expecc %d, received %d", expecc, result.Value)
		return false
	}

	return true
}

func testBoolObj(t *testing.T, obj object.Object, expecc bool) bool {
	result, ok := obj.(*object.Boolean)
	if !ok {
		t.Errorf("objecc is not boolean, received %T (%+v)", obj, obj)
		return false
	}

	if result.Value != expecc {
		t.Errorf("objecc has unexpecc value; expecc %t, received %t", expecc, result.Value)
		return false
	}
	return true
}
