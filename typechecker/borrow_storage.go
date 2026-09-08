package typechecker

import (
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
