package optir

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"hash"
)

// FingerprintCFG returns a canonical digest of every semantic field in a
// verified CFG. Ordered slices remain ordered, while nil and empty slices have
// the same representation. The digest identifies analysis inputs; it is not a
// semantic-verification verdict.
func FingerprintCFG(cfg CFG) (string, error) {
	if err := Verify(cfg); err != nil {
		return "", err
	}
	return fingerprintCFG(cfg), nil
}

func fingerprintCFG(cfg CFG) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.cfg.v1")
	fingerprintString(digest, cfg.Name)
	fingerprintUint64(digest, uint64(cfg.Entry))
	fingerprintUint64(digest, uint64(len(cfg.Results)))
	for _, result := range cfg.Results {
		fingerprintString(digest, string(result))
	}
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintBlock(digest, block)
	}
	fingerprintFacts(digest, cfg.Facts)
	return hex.EncodeToString(digest.Sum(nil))
}

func fingerprintLoopAnalysis(analysis LoopAnalysis) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.loops.v1")
	fingerprintString(digest, analysis.inputFingerprint)
	fingerprintUint64(digest, uint64(len(analysis.ReversePostOrder)))
	for _, block := range analysis.ReversePostOrder {
		fingerprintUint64(digest, uint64(block))
	}
	fingerprintUint64(digest, uint64(len(analysis.Dominators)))
	for _, dominator := range analysis.Dominators {
		fingerprintUint64(digest, uint64(dominator.Block))
		fingerprintUint64(digest, uint64(dominator.Immediate))
		fingerprintBool(digest, dominator.HasImmediate)
		fingerprintUint64(digest, uint64(int64(dominator.Depth)))
	}
	fingerprintUint64(digest, uint64(len(analysis.BackEdges)))
	for _, edge := range analysis.BackEdges {
		fingerprintFlowEdge(digest, edge)
	}
	fingerprintUint64(digest, uint64(len(analysis.Loops)))
	for _, loop := range analysis.Loops {
		fingerprintUint64(digest, uint64(loop.Header))
		fingerprintBlockIDs(digest, loop.Latches)
		fingerprintBlockIDs(digest, loop.Blocks)
		fingerprintUint64(digest, uint64(len(loop.Exits)))
		for _, edge := range loop.Exits {
			fingerprintFlowEdge(digest, edge)
		}
		fingerprintUint64(digest, uint64(loop.Preheader))
		fingerprintBool(digest, loop.HasPreheader)
		fingerprintUint64(digest, uint64(loop.Parent))
		fingerprintBool(digest, loop.HasParent)
		fingerprintUint64(digest, uint64(int64(loop.Depth)))
		fingerprintUint64(digest, uint64(len(loop.Inductions)))
		for _, induction := range loop.Inductions {
			fingerprintUint64(digest, uint64(induction.HeaderValue))
			fingerprintUint64(digest, uint64(int64(induction.ParameterIndex)))
			fingerprintUint64(digest, uint64(induction.Initial))
			fingerprintValueIDs(digest, induction.Updates)
			fingerprintString(digest, string(induction.Type))
			fingerprintString(digest, induction.Step)
			fingerprintUint64(digest, uint64(induction.Predicate))
			fingerprintUint64(digest, uint64(induction.Bound))
			fingerprintString(digest, induction.Comparison)
			fingerprintString(digest, induction.ExactTripCount)
			fingerprintBool(digest, induction.HasExactTripCount)
		}
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func fingerprintLoopStructure(structure LoopStructure) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.loop-structure.v1")
	fingerprintString(digest, structure.inputFingerprint)
	fingerprintBlockIDs(digest, structure.ReversePostOrder)
	fingerprintUint64(digest, uint64(len(structure.Dominators)))
	for _, dominator := range structure.Dominators {
		fingerprintUint64(digest, uint64(dominator.Block))
		fingerprintUint64(digest, uint64(dominator.Immediate))
		fingerprintBool(digest, dominator.HasImmediate)
		fingerprintUint64(digest, uint64(int64(dominator.Depth)))
	}
	fingerprintUint64(digest, uint64(len(structure.BackEdges)))
	for _, edge := range structure.BackEdges {
		fingerprintFlowEdge(digest, edge)
	}
	fingerprintUint64(digest, uint64(len(structure.Loops)))
	for _, loop := range structure.Loops {
		fingerprintUint64(digest, uint64(loop.Header))
		fingerprintBlockIDs(digest, loop.Latches)
		fingerprintBlockIDs(digest, loop.Blocks)
		fingerprintUint64(digest, uint64(len(loop.Exits)))
		for _, edge := range loop.Exits {
			fingerprintFlowEdge(digest, edge)
		}
		fingerprintUint64(digest, uint64(loop.Preheader))
		fingerprintBool(digest, loop.HasPreheader)
		fingerprintUint64(digest, uint64(loop.Parent))
		fingerprintBool(digest, loop.HasParent)
		fingerprintUint64(digest, uint64(int64(loop.Depth)))
		fingerprintUint64(digest, uint64(len(loop.Inductions)))
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func fingerprintBlockIDs(digest hash.Hash, blocks []BlockID) {
	fingerprintUint64(digest, uint64(len(blocks)))
	for _, block := range blocks {
		fingerprintUint64(digest, uint64(block))
	}
}

func fingerprintFlowEdge(digest hash.Hash, edge FlowEdge) {
	fingerprintUint64(digest, uint64(edge.From))
	fingerprintUint64(digest, uint64(edge.To))
}

func fingerprintBlock(digest hash.Hash, block Block) {
	fingerprintUint64(digest, uint64(block.ID))
	fingerprintValues(digest, block.Parameters)
	fingerprintUint64(digest, uint64(len(block.Operations)))
	for _, operation := range block.Operations {
		fingerprintOperation(digest, operation)
	}
	fingerprintTerminator(digest, block.Terminator)
}

func fingerprintOperation(digest hash.Hash, operation Operation) {
	fingerprintString(digest, operation.Code)
	fingerprintValues(digest, operation.Results)
	fingerprintValueIDs(digest, operation.Operands)
	fingerprintUint64(digest, uint64(len(operation.Effects)))
	for _, effect := range operation.Effects {
		fingerprintString(digest, string(effect))
	}
	fingerprintUint64(digest, uint64(len(operation.Attributes)))
	for _, attribute := range operation.Attributes {
		fingerprintString(digest, attribute.Name)
		fingerprintString(digest, attribute.Value)
	}
	fingerprintFacts(digest, operation.Facts)
	fingerprintSource(digest, operation.Source)
}

func fingerprintTerminator(digest hash.Hash, terminator Terminator) {
	fingerprintString(digest, string(terminator.Kind))
	fingerprintUint64(digest, uint64(terminator.Condition))
	fingerprintEdge(digest, terminator.True)
	fingerprintEdge(digest, terminator.False)
	fingerprintValueIDs(digest, terminator.Values)
}

func fingerprintEdge(digest hash.Hash, edge Edge) {
	fingerprintUint64(digest, uint64(edge.Target))
	fingerprintValueIDs(digest, edge.Arguments)
}

func fingerprintValues(digest hash.Hash, values []Value) {
	fingerprintUint64(digest, uint64(len(values)))
	for _, value := range values {
		fingerprintUint64(digest, uint64(value.ID))
		fingerprintString(digest, string(value.Type))
		fingerprintString(digest, value.Name)
		fingerprintSource(digest, value.Source)
	}
}

func fingerprintFacts(digest hash.Hash, facts []Fact) {
	fingerprintUint64(digest, uint64(len(facts)))
	for _, fact := range facts {
		fingerprintString(digest, fact.ID)
		fingerprintString(digest, fact.Name)
		fingerprintValueIDs(digest, fact.Values)
		fingerprintString(digest, fact.Provenance)
		fingerprintString(digest, fact.Witness)
		fingerprintString(digest, fact.Scope)
		fingerprintUint64(digest, uint64(len(fact.Dependencies)))
		for _, dependency := range fact.Dependencies {
			fingerprintString(digest, dependency)
		}
	}
}

func fingerprintValueIDs(digest hash.Hash, values []ValueID) {
	fingerprintUint64(digest, uint64(len(values)))
	for _, value := range values {
		fingerprintUint64(digest, uint64(value))
	}
}

func fingerprintSource(digest hash.Hash, source Source) {
	fingerprintString(digest, source.Context)
	fingerprintUint64(digest, uint64(int64(source.Line)))
	fingerprintUint64(digest, uint64(int64(source.Column)))
}

func fingerprintString(digest hash.Hash, value string) {
	fingerprintUint64(digest, uint64(len(value)))
	_, _ = digest.Write([]byte(value))
}

func fingerprintUint64(digest hash.Hash, value uint64) {
	var encoded [8]byte
	binary.BigEndian.PutUint64(encoded[:], value)
	_, _ = digest.Write(encoded[:])
}

func fingerprintBool(digest hash.Hash, value bool) {
	if value {
		fingerprintUint64(digest, 1)
		return
	}
	fingerprintUint64(digest, 0)
}
