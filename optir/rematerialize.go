package optir

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"hash"
	"math"
	"sort"
)

const (
	maxRematerializationDepth = 64
	maxRematerializationCost  = 64
)

// RematerializationDecision is target-independent evidence that one spilled
// SSA value may be reconstructed from a closed recipe instead of preserved in
// memory. Cost is the conservative number of semantic recipe operations per
// reconstruction; Uses is the exact syntactic SSA-use count used by the
// decision. Dependencies retain their semantic order.
type RematerializationDecision struct {
	Value        ValueID
	Code         string
	Dependencies []ValueID
	Cost         uint64
	Uses         uint64
}

// RematerializationPlan is tied to both the exact verified CFG and exact
// verified register plan. It is evidence for a later target decision, not an
// emission license.
type RematerializationPlan struct {
	CFGFingerprint      string
	RegisterFingerprint string
	Decisions           []RematerializationDecision
}

type rematerializationDefinition struct {
	operation Operation
	block     BlockID
	index     int
}

type rematerializationRecipe struct {
	code         string
	dependencies []ValueID
	cost         uint64
}

// AnalyzeRematerialization selects only spilled constants and copies whose
// complete dependency chain ends in constants. Calls, memory, traps, arbitrary
// pure arithmetic, parameters, and values participating in proof facts are
// deliberately outside this first closed vocabulary.
func AnalyzeRematerialization(cfg CFG, pool []int, fixed map[ValueID]int, registers RegisterPlan) (RematerializationPlan, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return RematerializationPlan{}, err
	}
	if err := VerifyRegisterPlan(cfg, pool, fixed, registers); err != nil {
		return RematerializationPlan{}, err
	}
	cfgFingerprint, err := FingerprintCFG(cfg)
	if err != nil {
		return RematerializationPlan{}, err
	}
	registerFingerprint, err := FingerprintRegisterPlan(cfg, pool, fixed, registers)
	if err != nil {
		return RematerializationPlan{}, err
	}
	decisions, err := canonicalRematerializationDecisions(cfg, registers)
	if err != nil {
		return RematerializationPlan{}, err
	}
	plan := RematerializationPlan{
		CFGFingerprint: cfgFingerprint, RegisterFingerprint: registerFingerprint, Decisions: decisions,
	}
	if err := VerifyRematerializationPlan(cfg, pool, fixed, registers, plan); err != nil {
		return RematerializationPlan{}, fmt.Errorf("optir: generated invalid rematerialization plan: %w", err)
	}
	return plan, nil
}

// VerifyRematerializationPlan independently rechecks the CFG and allocation,
// rejects malformed/cyclic evidence, then recomputes the unique canonical
// decision set. Nothing embedded in plan is trusted.
func VerifyRematerializationPlan(cfg CFG, pool []int, fixed map[ValueID]int, registers RegisterPlan, plan RematerializationPlan) error {
	if err := validateAnalysisCFG(cfg); err != nil {
		return err
	}
	if err := VerifyRegisterPlan(cfg, pool, fixed, registers); err != nil {
		return err
	}
	cfgFingerprint, err := FingerprintCFG(cfg)
	if err != nil {
		return err
	}
	if plan.CFGFingerprint != cfgFingerprint {
		return fmt.Errorf("optir: rematerialization CFG fingerprint is stale")
	}
	registerFingerprint, err := FingerprintRegisterPlan(cfg, pool, fixed, registers)
	if err != nil {
		return err
	}
	if plan.RegisterFingerprint != registerFingerprint {
		return fmt.Errorf("optir: rematerialization register-plan fingerprint is stale")
	}
	definitions := rematerializationDefinitions(cfg)
	if err := validateRematerializationEvidence(plan.Decisions, definitions, registers); err != nil {
		return err
	}
	expected, err := canonicalRematerializationDecisions(cfg, registers)
	if err != nil {
		return err
	}
	if !equalRematerializationDecisions(plan.Decisions, expected) {
		return fmt.Errorf("optir: rematerialization decisions are stale or forged")
	}
	return nil
}

// FingerprintRegisterPlan returns a canonical digest only after independently
// verifying the allocation against cfg, pool, and fixed ABI colors.
func FingerprintRegisterPlan(cfg CFG, pool []int, fixed map[ValueID]int, plan RegisterPlan) (string, error) {
	if err := VerifyRegisterPlan(cfg, pool, fixed, plan); err != nil {
		return "", err
	}
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.register-plan.v1")
	fingerprintString(digest, fingerprintCFG(cfg))
	colors := normalizedColors(pool)
	fingerprintUint64(digest, uint64(len(colors)))
	for _, color := range colors {
		fingerprintUint64(digest, uint64(int64(color)))
	}
	fingerprintValueIntMap(digest, fixed)
	fingerprintValueIntMap(digest, plan.Colors)
	fingerprintUint64(digest, uint64(len(plan.Spills)))
	for _, value := range sortedSpillValues(plan.Spills) {
		fingerprintUint64(digest, uint64(value))
		fingerprintUint64(digest, uint64(plan.Spills[value]))
	}
	fingerprintUint64(digest, uint64(len(plan.Slots)))
	for _, slot := range plan.Slots {
		fingerprintUint64(digest, uint64(slot.ID))
		fingerprintUint64(digest, uint64(slot.WidthBytes))
		fingerprintUint64(digest, uint64(slot.AlignmentBytes))
		fingerprintValueIDs(digest, slot.Values)
	}
	fingerprintValueLists(digest, plan.Interference)
	fingerprintBlockValueLists(digest, plan.LiveIn)
	fingerprintBlockValueLists(digest, plan.LiveOut)
	return hex.EncodeToString(digest.Sum(nil)), nil
}

func canonicalRematerializationDecisions(cfg CFG, registers RegisterPlan) ([]RematerializationDecision, error) {
	definitions := rematerializationDefinitions(cfg)
	uses := rematerializationUseCounts(cfg)
	factValues := rematerializationFactValues(cfg)
	values := sortedSpillValues(registers.Spills)
	var decisions []RematerializationDecision
	for _, value := range values {
		if factValues[value] || uses[value] == 0 {
			continue
		}
		recipe, ok, err := rematerializationRecipeFor(value, definitions, factValues, registers.Spills, map[ValueID]uint8{}, 0)
		if err != nil {
			return nil, err
		}
		if !ok || recipe.cost == 0 || recipe.cost > maxRematerializationCost {
			continue
		}
		useCount := uses[value]
		if useCount == math.MaxUint64 || recipe.cost > math.MaxUint64/useCount {
			continue
		}
		rematerializationCost := recipe.cost * useCount
		spillCost := useCount + 1 // one definition store plus one load per use
		if rematerializationCost > spillCost {
			continue
		}
		decisions = append(decisions, RematerializationDecision{
			Value: value, Code: recipe.code, Dependencies: append([]ValueID(nil), recipe.dependencies...), Cost: recipe.cost, Uses: useCount,
		})
	}
	return decisions, nil
}

func rematerializationRecipeFor(value ValueID, definitions map[ValueID]rematerializationDefinition, factValues map[ValueID]bool, spills map[ValueID]SpillSlotID, visiting map[ValueID]uint8, depth int) (rematerializationRecipe, bool, error) {
	if depth >= maxRematerializationDepth {
		return rematerializationRecipe{}, false, fmt.Errorf("optir: rematerialization dependency depth exceeds %d", maxRematerializationDepth)
	}
	if visiting[value] == 1 {
		return rematerializationRecipe{}, false, fmt.Errorf("optir: rematerialization dependency cycle at value %d", value)
	}
	defined, exists := definitions[value]
	if !exists || factValues[value] {
		return rematerializationRecipe{}, false, nil
	}
	operation := defined.operation
	if len(operation.Effects) != 0 || len(operation.Facts) != 0 || len(operation.Results) != 1 || operation.Results[0].ID != value {
		return rematerializationRecipe{}, false, nil
	}
	switch operation.Code {
	case OpConstBool, OpConstInt:
		if len(operation.Operands) != 0 {
			return rematerializationRecipe{}, false, nil
		}
		return rematerializationRecipe{code: operation.Code, cost: 1}, true, nil
	case OpCopy:
		if len(operation.Operands) != 1 || len(operation.Attributes) != 0 {
			return rematerializationRecipe{}, false, nil
		}
		dependency := operation.Operands[0]
		if _, spilled := spills[dependency]; !spilled {
			return rematerializationRecipe{}, false, nil
		}
		visiting[value] = 1
		recipe, ok, err := rematerializationRecipeFor(dependency, definitions, factValues, spills, visiting, depth+1)
		delete(visiting, value)
		if err != nil || !ok || recipe.cost >= maxRematerializationCost {
			return rematerializationRecipe{}, false, err
		}
		return rematerializationRecipe{code: operation.Code, dependencies: []ValueID{dependency}, cost: recipe.cost + 1}, true, nil
	default:
		return rematerializationRecipe{}, false, nil
	}
}

func validateRematerializationEvidence(decisions []RematerializationDecision, definitions map[ValueID]rematerializationDefinition, registers RegisterPlan) error {
	byValue := make(map[ValueID]RematerializationDecision, len(decisions))
	for index, decision := range decisions {
		if decision.Value == 0 || index > 0 && decisions[index-1].Value >= decision.Value {
			return fmt.Errorf("optir: rematerialization decisions are not strictly value-ordered")
		}
		if _, spilled := registers.Spills[decision.Value]; !spilled {
			return fmt.Errorf("optir: rematerialization value %d is not spilled", decision.Value)
		}
		defined, exists := definitions[decision.Value]
		if !exists || defined.operation.Code != decision.Code {
			return fmt.Errorf("optir: rematerialization value %d does not name its exact operation", decision.Value)
		}
		if decision.Cost == 0 || decision.Cost > maxRematerializationCost || decision.Uses == 0 {
			return fmt.Errorf("optir: rematerialization value %d has invalid cost/use evidence", decision.Value)
		}
		if decision.Code != OpConstBool && decision.Code != OpConstInt && decision.Code != OpCopy {
			return fmt.Errorf("optir: rematerialization value %d uses forbidden operation %s", decision.Value, decision.Code)
		}
		byValue[decision.Value] = decision
	}
	states := map[ValueID]uint8{}
	var visit func(ValueID) error
	visit = func(value ValueID) error {
		if states[value] == 1 {
			return fmt.Errorf("optir: rematerialization decision dependency cycle at value %d", value)
		}
		if states[value] == 2 {
			return nil
		}
		states[value] = 1
		for _, dependency := range byValue[value].Dependencies {
			if _, included := byValue[dependency]; included {
				if err := visit(dependency); err != nil {
					return err
				}
			}
		}
		states[value] = 2
		return nil
	}
	for value := range byValue {
		if err := visit(value); err != nil {
			return err
		}
	}
	return nil
}

func rematerializationDefinitions(cfg CFG) map[ValueID]rematerializationDefinition {
	out := map[ValueID]rematerializationDefinition{}
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			for _, result := range operation.Results {
				out[result.ID] = rematerializationDefinition{operation: operation, block: block.ID, index: index}
			}
		}
	}
	return out
}

func rematerializationUseCounts(cfg CFG) map[ValueID]uint64 {
	uses := map[ValueID]uint64{}
	note := func(value ValueID) {
		if uses[value] != math.MaxUint64 {
			uses[value]++
		}
	}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, operand := range operation.Operands {
				note(operand)
			}
		}
		for _, value := range terminatorUses(block.Terminator) {
			note(value)
		}
	}
	return uses
}

func rematerializationFactValues(cfg CFG) map[ValueID]bool {
	out := map[ValueID]bool{}
	for _, fact := range cfg.Facts {
		for _, value := range fact.Values {
			out[value] = true
		}
	}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			for _, fact := range operation.Facts {
				for _, value := range fact.Values {
					out[value] = true
				}
			}
		}
	}
	return out
}

func equalRematerializationDecisions(left, right []RematerializationDecision) bool {
	if len(left) != len(right) {
		return false
	}
	for index := range left {
		if left[index].Value != right[index].Value || left[index].Code != right[index].Code || left[index].Cost != right[index].Cost || left[index].Uses != right[index].Uses || len(left[index].Dependencies) != len(right[index].Dependencies) {
			return false
		}
		for dependency := range left[index].Dependencies {
			if left[index].Dependencies[dependency] != right[index].Dependencies[dependency] {
				return false
			}
		}
	}
	return true
}

func sortedSpillValues(values map[ValueID]SpillSlotID) []ValueID {
	out := make([]ValueID, 0, len(values))
	for value := range values {
		out = append(out, value)
	}
	sort.Slice(out, func(i, j int) bool { return out[i] < out[j] })
	return out
}

func fingerprintValueIntMap(digest hash.Hash, values map[ValueID]int) {
	keys := make([]ValueID, 0, len(values))
	for value := range values {
		keys = append(keys, value)
	}
	sort.Slice(keys, func(i, j int) bool { return keys[i] < keys[j] })
	fingerprintUint64(digest, uint64(len(keys)))
	for _, value := range keys {
		fingerprintUint64(digest, uint64(value))
		fingerprintUint64(digest, uint64(int64(values[value])))
	}
}

func fingerprintValueLists(digest hash.Hash, values map[ValueID][]ValueID) {
	keys := make([]ValueID, 0, len(values))
	for value := range values {
		keys = append(keys, value)
	}
	sort.Slice(keys, func(i, j int) bool { return keys[i] < keys[j] })
	fingerprintUint64(digest, uint64(len(keys)))
	for _, value := range keys {
		fingerprintUint64(digest, uint64(value))
		fingerprintValueIDs(digest, values[value])
	}
}

func fingerprintBlockValueLists(digest hash.Hash, values map[BlockID][]ValueID) {
	keys := make([]BlockID, 0, len(values))
	for block := range values {
		keys = append(keys, block)
	}
	sort.Slice(keys, func(i, j int) bool { return keys[i] < keys[j] })
	fingerprintUint64(digest, uint64(len(keys)))
	for _, block := range keys {
		fingerprintUint64(digest, uint64(block))
		fingerprintValueIDs(digest, values[block])
	}
}
