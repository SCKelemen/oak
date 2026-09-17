package wasm

import (
	"fmt"

	"github.com/SCKelemen/oak/optir"
)

// The byte checker starts with one function frame and admits at most 128
// frames. Keep one explicit frame available for operation-local lowering such
// as signed division's result-producing if.
const maxStructuredControlDepth = 126

type structuredRegionWork struct {
	region optir.Region
	depth  int
}

// validateStructuredLimits runs before OptIR's recursive validation and
// projection. It bounds hostile pointer-shaped trees and rejects shared/cyclic
// control nodes before recursive copying or emission can consume them.
func validateStructuredLimits(function optir.Function) error {
	work := []structuredRegionWork{{region: function.Body}}
	seenIf := map[*optir.If]bool{}
	seenWhile := map[*optir.While]bool{}
	nodes := 0
	for len(work) != 0 {
		item := work[len(work)-1]
		work = work[:len(work)-1]
		if item.depth > maxStructuredControlDepth {
			return fmt.Errorf("wasm: structured control depth exceeds scalar profile")
		}
		for _, node := range item.region.Nodes {
			nodes++
			if nodes > 16384 {
				return fmt.Errorf("wasm: structured node count exceeds scalar profile")
			}
			members := 0
			if node.Operation != nil {
				members++
			}
			if node.If != nil {
				members++
				if seenIf[node.If] {
					return fmt.Errorf("wasm: structured conditional is shared or cyclic")
				}
				seenIf[node.If] = true
				work = append(work,
					structuredRegionWork{region: node.If.Then, depth: item.depth + 1},
					structuredRegionWork{region: node.If.Else, depth: item.depth + 1},
				)
			}
			if node.While != nil {
				members++
				if seenWhile[node.While] {
					return fmt.Errorf("wasm: structured loop is shared or cyclic")
				}
				seenWhile[node.While] = true
				work = append(work,
					structuredRegionWork{region: node.While.Condition, depth: item.depth + 2},
					structuredRegionWork{region: node.While.Body, depth: item.depth + 2},
				)
			}
			if members != 1 {
				return fmt.Errorf("wasm: structured node must contain exactly one operation, if, or while")
			}
		}
	}
	return nil
}

// bindStructuredArguments maps lexical loop-region arguments onto the same
// locals as their carried results. They are read-only SSA names for the
// current iteration, so aliases avoid adding unused locals to established raw
// CFG encodings.
func (f *function) bindStructuredArguments() error {
	var bindRegion func(optir.Region) error
	bindValue := func(value optir.Value) error {
		if got, ok := f.types[value.ID]; !ok || got != value.Type {
			return fmt.Errorf("structured value %d is absent from its CFG projection", value.ID)
		}
		return nil
	}
	alias := func(argument, result optir.Value) error {
		local, ok := f.locals[result.ID]
		if !ok || f.types[result.ID] != argument.Type || result.Type != argument.Type {
			return fmt.Errorf("structured carried value %d has no matching CFG local", result.ID)
		}
		if _, exists := f.locals[argument.ID]; exists {
			return fmt.Errorf("structured region argument %d collides with a CFG value", argument.ID)
		}
		f.locals[argument.ID] = local
		f.types[argument.ID] = argument.Type
		return nil
	}
	bindRegion = func(region optir.Region) error {
		for _, node := range region.Nodes {
			switch {
			case node.Operation != nil:
				for _, result := range node.Operation.Results {
					if err := bindValue(result); err != nil {
						return err
					}
				}
			case node.If != nil:
				for _, result := range node.If.Results {
					if err := bindValue(result); err != nil {
						return err
					}
				}
				if err := bindRegion(node.If.Then); err != nil {
					return err
				}
				if err := bindRegion(node.If.Else); err != nil {
					return err
				}
			case node.While != nil:
				loop := node.While
				for i, result := range loop.Results {
					if err := bindValue(result); err != nil {
						return err
					}
					if err := alias(loop.Condition.Arguments[i], result); err != nil {
						return err
					}
					if err := alias(loop.Body.Arguments[i], result); err != nil {
						return err
					}
				}
				if err := bindRegion(loop.Condition); err != nil {
					return err
				}
				if err := bindRegion(loop.Body); err != nil {
					return err
				}
			}
		}
		return nil
	}
	return bindRegion(f.structured.Body)
}

func (f *function) structuredBody(b *binary, functions map[string]*function) error {
	if err := f.structuredRegion(b, f.structured.Body, functions); err != nil {
		return err
	}
	if f.cfg.Results[0] != "()" {
		f.get(b, f.structured.Body.Yield[0])
	}
	b.op(0x0b) // function end
	return nil
}

func (f *function) structuredRegion(b *binary, region optir.Region, functions map[string]*function) error {
	for _, node := range region.Nodes {
		switch {
		case node.Operation != nil:
			if err := f.operation(b, *node.Operation, functions); err != nil {
				return err
			}
		case node.If != nil:
			branch := node.If
			f.get(b, branch.Condition)
			b.op(0x04, 0x40) // if, empty block type; results live in locals
			if err := f.structuredRegion(b, branch.Then, functions); err != nil {
				return err
			}
			f.parallelValues(b, branch.Results, branch.Then.Yield)
			b.op(0x05) // else
			if err := f.structuredRegion(b, branch.Else, functions); err != nil {
				return err
			}
			f.parallelValues(b, branch.Results, branch.Else.Yield)
			b.op(0x0b)
		case node.While != nil:
			loop := node.While
			f.parallelValues(b, loop.Results, loop.Initial)
			b.op(0x02, 0x40, 0x03, 0x40) // exit block; repeating loop
			if err := f.structuredRegion(b, loop.Condition, functions); err != nil {
				return err
			}
			f.get(b, loop.Condition.Yield[0])
			b.op(0x45, 0x0d, 0x01) // i32.eqz; br_if exit block
			if err := f.structuredRegion(b, loop.Body, functions); err != nil {
				return err
			}
			f.parallelValues(b, loop.Results, loop.Body.Yield)
			b.op(0x0c, 0x00, 0x0b, 0x0b) // continue; end loop and exit
		default:
			return fmt.Errorf("unsupported empty structured node")
		}
	}
	return nil
}

func (f *function) parallelValues(b *binary, destinations []optir.Value, sources []optir.ValueID) {
	// Snapshot every source before writing any destination: loop-carried swaps
	// and multi-result control nodes have simultaneous SSA edge semantics.
	for _, source := range sources {
		f.get(b, source)
	}
	for i := len(destinations) - 1; i >= 0; i-- {
		b.local(0x21, f.locals[destinations[i].ID])
	}
}
