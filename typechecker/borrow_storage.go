package typechecker

import (
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/object"
)

// borrowTypeInfo retains checked expression types after local scopes close.
// Borrow checking consumes this information without re-running inference.
type borrowTypeInfo struct {
	payloads     map[string]map[string]Type
	adts         map[string]*object.ADTType
	expressions  map[ast.Expression]Type
	declarations map[*ast.VariableDeclaration]Type
	simdCalls    map[*ast.InvocationExpression]string
	// regions is the erased region structure of functions and records
	// (typechecker/regions.go), read by the borrow checker.
	regions *regionInfo
}

func (e *TypeEnvironment) borrowMetadata() *borrowTypeInfo {
	for e != nil {
		if e.borrowInfo != nil {
			return e.borrowInfo
		}
		e = e.outer
	}
	return nil
}

// CheckedExpressionType returns the type recorded during successful checking.
func (e *TypeEnvironment) CheckedExpressionType(expr ast.Expression) Type {
	if info := e.borrowMetadata(); info != nil {
		return info.expressions[expr]
	}
	return nil
}

// CheckedDeclarationType includes declarations without initializers.
func (e *TypeEnvironment) CheckedDeclarationType(stmt *ast.VariableDeclaration) Type {
	if info := e.borrowMetadata(); info != nil {
		return info.declarations[stmt]
	}
	return nil
}

// ContainsBorrowStorage examines storage, including instantiated ADT payloads.
// Type arguments alone are not storage: phantom parameters remain borrow-free.
// GADT variants are considered conservatively, even when an index equation
// might make a variant unreachable.
func (e *TypeEnvironment) ContainsBorrowStorage(typ Type) bool {
	info := e.borrowMetadata()
	active := make(map[string]bool)
	type storageNode struct {
		typ     Type
		context string
	}
	structural := make(map[storageNode]bool)
	context := ""
	var visit func(Type, map[string]bool) bool
	visit = func(typ Type, bindings map[string]bool) bool {
		if typ == nil {
			return false
		}
		switch t := typ.(type) {
		case *StringType:
			return true
		case *ArrayType:
			if t.IsSlice || t.IsSpan {
				return true
			}
		case *ADTType:
			if borrowed, parameter := bindings[t.Name]; parameter {
				return borrowed
			}
		}
		if name, _, args, nominal := adtInstantiation(typ); nominal && info != nil {
			def := info.adts[name]
			if def == nil {
				return false
			}
			// Abstract arguments to borrow presence. This finite state space
			// terminates even for expanding recursion such as F[F[T]].
			next := make(map[string]bool)
			key := name + ":"
			for i, parameter := range def.TypeParams {
				borrowed := i < len(args) && visit(args[i], bindings)
				next[parameter] = borrowed
				if borrowed {
					key += "1"
				} else {
					key += "0"
				}
			}
			if active[key] {
				return false
			}
			active[key] = true
			defer delete(active, key)
			previous := context
			context = key
			defer func() { context = previous }()
			for _, variant := range def.Variants {
				if visit(info.payloads[name][variant.Name], next) {
					return true
				}
			}
			return false
		}
		node := storageNode{typ, context}
		if structural[node] {
			return false
		}
		structural[node] = true
		defer delete(structural, node)
		switch t := typ.(type) {
		case *ArrayType:
			return visit(t.ElementType, bindings)
		case *RecordType:
			for _, field := range t.Fields {
				if visit(field, bindings) {
					return true
				}
			}
		case *UnionType:
			for _, member := range t.Types {
				if visit(member, bindings) {
					return true
				}
			}
		case *IntersectionType:
			for _, member := range t.Types {
				if visit(member, bindings) {
					return true
				}
			}
		}
		return false
	}
	return visit(typ, nil)
}

// CheckedSIMDOperation identifies a resolved builtin, never a shadowing field.
// SIMD stores affect only their explicit span; no SIMD operation writes an
// unrelated global owner. Borrow checking uses this after local scopes close.
func (e *TypeEnvironment) CheckedSIMDOperation(call *ast.InvocationExpression) string {
	if info := e.borrowMetadata(); info != nil {
		return info.simdCalls[call]
	}
	return ""
}

// BorrowPath is one piece of borrowed storage inside a value: the dotted
// path to it (fields by name, a variant's payload as `$Variant`, the empty
// path for the value itself) and whether it is writable.
type BorrowPath struct {
	Path string
	Span bool
}

// BorrowPaths lists every view or span a value of the type carries, by
// path, so the borrow checker can name a binding's borrows field by field
// and variant by variant (docs/spec/50-borrowing.md sections 8b, 8c).
// Reports false when the type carries borrowed storage the path form does
// not cover (strings, unions), so callers fail closed.
func (e *TypeEnvironment) BorrowPaths(typ Type) ([]BorrowPath, bool) {
	info := e.borrowMetadata()
	var paths []BorrowPath
	complete := true
	active := make(map[string]bool)
	var visit func(typ Type, prefix string, bindings map[string]Type, depth int)
	visit = func(typ Type, prefix string, bindings map[string]Type, depth int) {
		if typ == nil || depth > 16 {
			return
		}
		switch t := typ.(type) {
		case *StringType:
			complete = false
			return
		case *UnionType:
			for _, member := range t.Types {
				if e.ContainsBorrowStorage(member) {
					complete = false
					return
				}
			}
			return
		case *ArrayType:
			if t.IsSlice || t.IsSpan {
				paths = append(paths, BorrowPath{Path: prefix, Span: t.IsSpan})
				return
			}
			if e.ContainsBorrowStorage(t.ElementType) {
				// Arrays of borrows have no per-element path.
				complete = false
			}
			return
		case *RecordType:
			names := t.Order
			if len(names) == 0 {
				for name := range t.Fields {
					names = append(names, name)
				}
				sort.Strings(names)
			}
			for _, name := range names {
				visit(t.Fields[name], join(prefix, name), bindings, depth+1)
			}
			return
		case *ADTType:
			if bound, isParameter := bindings[t.Name]; isParameter {
				visit(bound, prefix, nil, depth+1)
				return
			}
		}
		name, _, args, nominal := adtInstantiation(typ)
		if !nominal || info == nil {
			return
		}
		def := info.adts[name]
		if def == nil {
			return
		}
		key := name + ":" + prefix
		if active[key] {
			return
		}
		active[key] = true
		defer delete(active, key)
		next := make(map[string]Type)
		for i, parameter := range def.TypeParams {
			if i < len(args) {
				next[parameter] = substituteBindings(args[i], bindings)
			}
		}
		for _, variant := range def.Variants {
			payload := info.payloads[name][variant.Name]
			if payload == nil {
				continue
			}
			visit(payload, join(prefix, "$"+variant.Name), next, depth+1)
		}
	}
	visit(typ, "", nil, 0)
	return paths, complete
}

func join(prefix, name string) string {
	if prefix == "" {
		return name
	}
	return prefix + "." + name
}

// substituteBindings replaces bound type-parameter placeholders.
func substituteBindings(typ Type, bindings map[string]Type) Type {
	if len(bindings) == 0 {
		return typ
	}
	if t, ok := typ.(*ADTType); ok {
		if bound, isParameter := bindings[t.Name]; isParameter {
			return bound
		}
	}
	return typ
}
