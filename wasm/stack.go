package wasm

import (
	"fmt"

	"github.com/SCKelemen/oak/optir"
)

type stackUse struct {
	block    optir.BlockID
	consumer string
}

type stackDefinition struct {
	block     optir.BlockID
	operation optir.Operation
}

// planStackExpressions finds total, effect-free definitions whose one runtime
// SSA use is in the defining block. Such a definition can be emitted directly
// at that use without duplicating execution or crossing a control-flow edge.
func (f *function) planStackExpressions() {
	definitions := map[optir.ValueID]stackDefinition{}
	uses := map[optir.ValueID][]stackUse{}
	use := func(block optir.BlockID, consumer string, values ...optir.ValueID) {
		for _, value := range values {
			uses[value] = append(uses[value], stackUse{block: block, consumer: consumer})
		}
	}
	for _, block := range f.cfg.Blocks {
		for _, operation := range block.Operations {
			if len(operation.Results) == 1 {
				definitions[operation.Results[0].ID] = stackDefinition{block: block.ID, operation: operation}
			}
			use(block.ID, operation.Code, operation.Operands...)
		}
		switch terminator := block.Terminator; terminator.Kind {
		case optir.TerminatorReturn:
			use(block.ID, "terminator.return", terminator.Values...)
		case optir.TerminatorBranch:
			use(block.ID, "terminator.edge", terminator.True.Arguments...)
		case optir.TerminatorCondBranch:
			use(block.ID, "terminator.condition", terminator.Condition)
			use(block.ID, "terminator.edge", terminator.True.Arguments...)
			use(block.ID, "terminator.edge", terminator.False.Arguments...)
		}
	}
	f.stackDefinitions = map[optir.ValueID]optir.Operation{}
	for id, definition := range definitions {
		operation := definition.operation
		valueUses := uses[id]
		if len(valueUses) != 1 || valueUses[0].block != definition.block ||
			len(operation.Effects) != 0 || operation.MemoryAccessID != "" || operation.MemoryCallID != "" ||
			operation.Code == optir.OpCall || operation.Code == optir.OpIntDiv || operation.Code == optir.OpIntRem ||
			valueUses[0].consumer == optir.OpIntDiv || valueUses[0].consumer == optir.OpIntRem {
			continue
		}
		f.stackDefinitions[id] = operation
	}
}

// compactStackLocals removes only locals belonging to deferred definitions.
// Parameter indices stay fixed. Every retained CFG value and structured lexical
// alias is remapped through its old physical local, so aliasing remains exact.
func (f *function) compactStackLocals() error {
	if len(f.stackDefinitions) == 0 {
		return nil
	}
	removed := map[uint32]bool{}
	for id := range f.stackDefinitions {
		local, ok := f.locals[id]
		if !ok || local < uint32(len(f.entry.Parameters)) {
			return fmt.Errorf("stack expression %d has no removable result local", id)
		}
		removed[local] = true
	}
	oldToNew := map[uint32]uint32{}
	localTypes := make([]byte, 0, len(f.localTypes)-len(removed))
	for old, typ := range f.localTypes {
		if removed[uint32(old)] {
			continue
		}
		oldToNew[uint32(old)] = uint32(len(localTypes))
		localTypes = append(localTypes, typ)
	}
	for id, old := range f.locals {
		if next, ok := oldToNew[old]; ok {
			f.locals[id] = next
			continue
		}
		if _, planned := f.stackDefinitions[id]; planned {
			delete(f.locals, id)
			continue
		}
		return fmt.Errorf("retained value %d aliases a removed stack-expression local", id)
	}
	f.localTypes = localTypes
	f.stackActive = map[optir.ValueID]bool{}
	f.stackConsumed = map[optir.ValueID]bool{}
	return nil
}

func (f *function) emitValue(b *binary, id optir.ValueID, functions map[string]*function) error {
	operation, planned := f.stackDefinitions[id]
	if !planned {
		local, ok := f.locals[id]
		if !ok {
			return fmt.Errorf("value %d has no Wasm local or stack expression", id)
		}
		b.local(0x20, local)
		return nil
	}
	if f.stackActive[id] {
		return fmt.Errorf("cyclic stack expression at value %d", id)
	}
	if f.stackConsumed[id] {
		return fmt.Errorf("stack expression %d was emitted more than once", id)
	}
	f.stackActive[id] = true
	f.stackConsumed[id] = true
	err := f.emitOperation(b, operation, functions, false)
	delete(f.stackActive, id)
	return err
}

// discardValue accounts for a deferred pure tree whose Oak Unit result has no
// Core Wasm carrier. Non-deferred dependencies have already executed in their
// source position; calls, traps and effects are never eligible for this path.
func (f *function) discardValue(id optir.ValueID) error {
	operation, planned := f.stackDefinitions[id]
	if !planned {
		return nil
	}
	if f.stackActive[id] {
		return fmt.Errorf("cyclic discarded stack expression at value %d", id)
	}
	if f.stackConsumed[id] {
		return fmt.Errorf("stack expression %d was consumed more than once", id)
	}
	f.stackActive[id] = true
	f.stackConsumed[id] = true
	for _, operand := range operation.Operands {
		if err := f.discardValue(operand); err != nil {
			return err
		}
	}
	delete(f.stackActive, id)
	return nil
}

func (f *function) validateStackExpressions() error {
	if len(f.stackActive) != 0 {
		return fmt.Errorf("stack-expression emission ended with an active cycle")
	}
	var missing optir.ValueID
	found := false
	for id := range f.stackDefinitions {
		if f.stackConsumed[id] {
			continue
		}
		if !found || id < missing {
			missing = id
			found = true
		}
	}
	if found {
		return fmt.Errorf("stack expression %d was not emitted", missing)
	}
	return nil
}
