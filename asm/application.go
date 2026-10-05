package asm

import (
	"fmt"
	"strconv"
	"strings"
)

// applyTerm builds an n-ary uninterpreted application. Applications are
// distinguished by their name, result width, arity, and argument widths;
// the decider gives them no property except congruence.
func applyTerm(name string, width int, args ...*term) *term {
	if name == "" || width < 1 || width > 64 {
		panic(fmt.Sprintf("applyTerm: %q at width %d over %d operands", name, width, len(args)))
	}
	owned := make([]*term, len(args))
	copy(owned, args)
	for i, arg := range owned {
		if arg == nil || arg.width < 1 || arg.width > 64 {
			panic(fmt.Sprintf("applyTerm: %q has invalid operand %d", name, i))
		}
	}
	return &term{kind: termApply, name: name, width: width, args: owned}
}

// applicationSpan is the uninterpreted-function namespace used by the
// Ackermann table. Length-prefixing the name and recording every width keeps
// different signatures disjoint even when their flattened argument bits are
// identical.
func applicationSpan(name string, width int, args []*term) string {
	var b strings.Builder
	b.WriteString("@apply:")
	b.WriteString(strconv.Itoa(len(name)))
	b.WriteByte(':')
	b.WriteString(name)
	b.WriteByte(':')
	b.WriteString(strconv.Itoa(width))
	for _, arg := range args {
		b.WriteByte(':')
		b.WriteString(strconv.Itoa(arg.width))
	}
	return b.String()
}

// applicationValue gives witness execution a deterministic interpretation of
// an otherwise uninterpreted function. It is evidence only: proof authority is
// the Ackermann congruence constraint in the blaster. Signature boundaries are
// mixed explicitly so equal applications evaluate equally and each argument
// position participates in the witness value.
func applicationValue(name string, width int, values []uint64, widths []int) uint64 {
	if len(values) != len(widths) {
		panic(fmt.Sprintf("applicationValue: %q has %d values and %d widths", name, len(values), len(widths)))
	}
	h := applicationValueStart(name, width, len(values))
	for i, value := range values {
		argWidth := widths[i]
		h = applicationValueWord(h, uint64(argWidth))
		h = applicationValueWord(h, value&mask(argWidth))
	}
	return h & mask(width)
}

func applicationValueStart(name string, width, arity int) uint64 {
	h := uint64(1469598103934665603)
	for i := 0; i < len(name); i++ {
		h = applicationValueByte(h, name[i])
	}
	h = applicationValueWord(h, uint64(width))
	return applicationValueWord(h, uint64(arity))
}

func applicationValueByte(h uint64, value byte) uint64 {
	return (h ^ uint64(value)) * uint64(1099511628211)
}

func applicationValueWord(h, value uint64) uint64 {
	for i := 0; i < 8; i++ {
		h = applicationValueByte(h, byte(value>>uint(8*i)))
	}
	return h
}

func equalTermArgsMemo(a, b []*term, memo map[[2]*term]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if !equalTermsMemo(a[i], b[i], memo) {
			return false
		}
	}
	return true
}

// rewriteTermArgs applies rewrite in order and preserves the original slice
// when no argument changes, so large shared application DAGs stay shared.
func rewriteTermArgs(args []*term, rewrite func(*term) *term) ([]*term, bool) {
	var out []*term
	for i, arg := range args {
		next := rewrite(arg)
		if out == nil && next != arg {
			out = make([]*term, len(args))
			copy(out, args[:i])
		}
		if out != nil {
			out[i] = next
		}
	}
	if out == nil {
		return args, false
	}
	return out, true
}
