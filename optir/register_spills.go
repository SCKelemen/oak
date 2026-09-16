package optir

import (
	"fmt"
	"sort"
)

// SpillSlotID identifies one abstract stack slot. It has no target offset;
// targets may materialize a verified plan using their own frame convention.
// Zero is invalid so missing spill assignments fail closed.
type SpillSlotID uint32

// SpillSlot describes one target-neutral scalar stack slot. Values may share a
// slot only when their storage layout agrees and their live ranges do not
// interfere.
type SpillSlot struct {
	ID             SpillSlotID
	WidthBytes     uint8
	AlignmentBytes uint8
	Values         []ValueID
}

// RegisterPlan partitions every non-Unit SSA value between a physical color
// and an abstract spill slot. Interference and liveness are retained as
// independently reproducible evidence; this plan does not insert loads,
// stores, stack offsets, or machine instructions.
type RegisterPlan struct {
	Colors       map[ValueID]int
	Spills       map[ValueID]SpillSlotID
	Slots        []SpillSlot
	Interference map[ValueID][]ValueID
	LiveIn       map[BlockID][]ValueID
	LiveOut      map[BlockID][]ValueID
}

type spillLayout struct {
	width     uint8
	alignment uint8
}

// PlanRegisters computes a deterministic finite-register plan. Unlike
// ColorRegisters, pressure is represented by explicit abstract spills rather
// than refusal. ABI precolors are never spill candidates.
func PlanRegisters(cfg CFG, pool []int, fixed map[ValueID]int) (RegisterPlan, error) {
	problem, err := analyzeRegisterProblem(cfg)
	if err != nil {
		return RegisterPlan{}, err
	}
	colors := normalizedColors(pool)
	if len(colors) == 0 {
		return RegisterPlan{}, fmt.Errorf("optir: register spill plan has no colors")
	}
	if err := validateFixedColors(problem.types, colors, fixed); err != nil {
		return RegisterPlan{}, err
	}
	if err := validateFixedInterference(problem.graph, fixed); err != nil {
		return RegisterPlan{}, err
	}
	layouts := make(map[ValueID]spillLayout, len(problem.graph))
	for value := range problem.graph {
		layout, ok := scalarSpillLayout(problem.types[value])
		if !ok {
			return RegisterPlan{}, fmt.Errorf("optir: register spill plan has no canonical scalar layout for value %d of type %q", value, problem.types[value])
		}
		layouts[value] = layout
	}

	active := make(map[ValueID]bool, len(problem.graph))
	for value := range problem.graph {
		active[value] = true
	}
	spilled := map[ValueID]bool{}
	var assignment map[ValueID]int
	for {
		var failed ValueID
		assignment, failed = colorRegisterGraph(problem, colors, fixed, active, true)
		if failed == 0 {
			break
		}
		victim, found := chooseSpillVictim(problem, active, fixed, failed)
		if !found {
			return RegisterPlan{}, fmt.Errorf("optir: fixed register pressure cannot be spilled")
		}
		delete(active, victim)
		spilled[victim] = true
	}

	spillMap, slots := allocateSpillSlots(problem.graph, layouts, spilled)
	coloring := registerColoring(problem, assignment)
	plan := RegisterPlan{
		Colors:       assignment,
		Spills:       spillMap,
		Slots:        slots,
		Interference: coloring.Interference,
		LiveIn:       coloring.LiveIn,
		LiveOut:      coloring.LiveOut,
	}
	if err := VerifyRegisterPlan(cfg, colors, fixed, plan); err != nil {
		return RegisterPlan{}, fmt.Errorf("optir: generated invalid register spill plan: %w", err)
	}
	return plan, nil
}

func chooseSpillVictim(problem registerProblem, active map[ValueID]bool, fixed map[ValueID]int, failed ValueID) (ValueID, bool) {
	var best ValueID
	found := false
	candidates := map[ValueID]bool{failed: true}
	for neighbor := range problem.graph[failed] {
		if active[neighbor] {
			candidates[neighbor] = true
		}
	}
	for value := range candidates {
		if _, precolored := fixed[value]; precolored {
			continue
		}
		if !found || spillVictimLess(problem, active, value, best) {
			best, found = value, true
		}
	}
	return best, found
}

// A lower reference/liveness weight is cheaper to spill. Equal-cost values
// prefer higher-degree removal because it resolves more interference; the
// final ValueID ordering makes the decision reproducible.
func spillVictimLess(problem registerProblem, active map[ValueID]bool, left, right ValueID) bool {
	if problem.spillWeight[left] != problem.spillWeight[right] {
		return problem.spillWeight[left] < problem.spillWeight[right]
	}
	leftDegree := activeDegree(problem.graph, left, active)
	rightDegree := activeDegree(problem.graph, right, active)
	if leftDegree != rightDegree {
		return leftDegree > rightDegree
	}
	return left < right
}

func allocateSpillSlots(graph map[ValueID]map[ValueID]bool, layouts map[ValueID]spillLayout, spilled map[ValueID]bool) (map[ValueID]SpillSlotID, []SpillSlot) {
	values := make([]ValueID, 0, len(spilled))
	for value := range spilled {
		values = append(values, value)
	}
	sort.Slice(values, func(i, j int) bool {
		left, right := layouts[values[i]], layouts[values[j]]
		if left.alignment != right.alignment {
			return left.alignment > right.alignment
		}
		if left.width != right.width {
			return left.width > right.width
		}
		return values[i] < values[j]
	})

	assignments := make(map[ValueID]SpillSlotID, len(values))
	var slots []SpillSlot
	for _, value := range values {
		layout := layouts[value]
		placed := false
		for index := range slots {
			slot := &slots[index]
			if slot.WidthBytes != layout.width || slot.AlignmentBytes != layout.alignment {
				continue
			}
			safe := true
			for _, other := range slot.Values {
				if graph[value][other] {
					safe = false
					break
				}
			}
			if safe {
				slot.Values = append(slot.Values, value)
				assignments[value] = slot.ID
				placed = true
				break
			}
		}
		if !placed {
			id := SpillSlotID(len(slots) + 1)
			slots = append(slots, SpillSlot{ID: id, WidthBytes: layout.width, AlignmentBytes: layout.alignment, Values: []ValueID{value}})
			assignments[value] = id
		}
	}
	for index := range slots {
		sort.Slice(slots[index].Values, func(i, j int) bool { return slots[index].Values[i] < slots[index].Values[j] })
	}
	return assignments, slots
}

// VerifyRegisterPlan independently reconstructs the liveness/interference
// problem and validates that the plan resolves every edge. It deliberately
// does not trust the evidence maps embedded in plan.
func VerifyRegisterPlan(cfg CFG, pool []int, fixed map[ValueID]int, plan RegisterPlan) error {
	problem, err := analyzeRegisterProblem(cfg)
	if err != nil {
		return err
	}
	colors := normalizedColors(pool)
	if len(colors) == 0 {
		return fmt.Errorf("optir: register spill plan has no colors")
	}
	if err := validateFixedColors(problem.types, colors, fixed); err != nil {
		return err
	}
	if err := validateFixedInterference(problem.graph, fixed); err != nil {
		return err
	}
	if !equalValueListsMap(plan.Interference, sortedInterference(problem.graph)) {
		return fmt.Errorf("optir: register spill plan interference evidence is stale")
	}
	if !equalValueListsMap(plan.LiveIn, problem.liveIn) || !equalValueListsMap(plan.LiveOut, problem.liveOut) {
		return fmt.Errorf("optir: register spill plan liveness evidence is stale")
	}

	allowed := map[int]bool{}
	for _, color := range colors {
		allowed[color] = true
	}
	for value := range problem.graph {
		color, colored := plan.Colors[value]
		slot, spilled := plan.Spills[value]
		if colored == spilled {
			return fmt.Errorf("optir: value %d must have exactly one register or spill assignment", value)
		}
		if colored && !allowed[color] {
			return fmt.Errorf("optir: value %d has color %d outside the pool", value, color)
		}
		if spilled && slot == 0 {
			return fmt.Errorf("optir: value %d has invalid spill slot zero", value)
		}
	}
	for value := range plan.Colors {
		if problem.graph[value] == nil {
			return fmt.Errorf("optir: register assignment names undefined or Unit value %d", value)
		}
	}
	for value := range plan.Spills {
		if problem.graph[value] == nil {
			return fmt.Errorf("optir: spill assignment names undefined or Unit value %d", value)
		}
	}
	for value, color := range fixed {
		if plan.Colors[value] != color {
			return fmt.Errorf("optir: fixed value %d changed color from %d", value, color)
		}
		if _, spilled := plan.Spills[value]; spilled {
			return fmt.Errorf("optir: fixed value %d was spilled", value)
		}
	}
	for left, neighbors := range problem.graph {
		leftColor, leftColored := plan.Colors[left]
		for right := range neighbors {
			if left < right {
				rightColor, rightColored := plan.Colors[right]
				if leftColored && rightColored && leftColor == rightColor {
					return fmt.Errorf("optir: interfering values %d and %d share color %d", left, right, leftColor)
				}
			}
		}
	}

	slots := map[SpillSlotID]SpillSlot{}
	for index, slot := range plan.Slots {
		wantID := SpillSlotID(index + 1)
		if slot.ID != wantID {
			return fmt.Errorf("optir: spill slot %d is noncanonical; expected %d", slot.ID, wantID)
		}
		if len(slot.Values) == 0 {
			return fmt.Errorf("optir: spill slot %d is empty", slot.ID)
		}
		if _, duplicate := slots[slot.ID]; duplicate {
			return fmt.Errorf("optir: duplicate spill slot %d", slot.ID)
		}
		for valueIndex, value := range slot.Values {
			if valueIndex > 0 && slot.Values[valueIndex-1] >= value {
				return fmt.Errorf("optir: spill slot %d values are not strictly ordered", slot.ID)
			}
			if plan.Spills[value] != slot.ID {
				return fmt.Errorf("optir: spill slot %d disagrees with value %d assignment", slot.ID, value)
			}
			layout, ok := scalarSpillLayout(problem.types[value])
			if !ok || slot.WidthBytes != layout.width || slot.AlignmentBytes != layout.alignment {
				return fmt.Errorf("optir: spill slot %d has wrong layout for value %d", slot.ID, value)
			}
			for _, other := range slot.Values[valueIndex+1:] {
				if problem.graph[value][other] {
					return fmt.Errorf("optir: interfering spilled values %d and %d share slot %d", value, other, slot.ID)
				}
			}
		}
		slots[slot.ID] = slot
	}
	for value, slot := range plan.Spills {
		if _, exists := slots[slot]; !exists {
			return fmt.Errorf("optir: value %d names missing spill slot %d", value, slot)
		}
	}
	return nil
}

func scalarSpillLayout(typ Type) (spillLayout, bool) {
	if typ == TypeBool {
		return spillLayout{width: 1, alignment: 1}, true
	}
	_, bits, ok := integerType(typ)
	if !ok || bits < 8 || bits > 64 || bits%8 != 0 {
		return spillLayout{}, false
	}
	bytes := uint8(bits / 8)
	return spillLayout{width: bytes, alignment: bytes}, true
}

func sortedInterference(graph map[ValueID]map[ValueID]bool) map[ValueID][]ValueID {
	out := make(map[ValueID][]ValueID, len(graph))
	for value, neighbors := range graph {
		for neighbor := range neighbors {
			out[value] = append(out[value], neighbor)
		}
		sort.Slice(out[value], func(i, j int) bool { return out[value][i] < out[value][j] })
	}
	return out
}

func equalValueListsMap[K comparable](left, right map[K][]ValueID) bool {
	if len(left) != len(right) {
		return false
	}
	for key, leftValues := range left {
		rightValues, exists := right[key]
		if !exists || len(leftValues) != len(rightValues) {
			return false
		}
		for index := range leftValues {
			if leftValues[index] != rightValues[index] {
				return false
			}
		}
	}
	return true
}
