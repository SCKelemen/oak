package optir

import (
	"fmt"
	"math/big"
	"sort"
	"strconv"
	"strings"
)

// LatticeState is one value's state in sparse conditional constant
// propagation. Unknown means no executable definition has established a value;
// Constant is one exact Oak value; Overdefined means it is not one constant.
type LatticeState string

const (
	LatticeUnknown     LatticeState = "unknown"
	LatticeConstant    LatticeState = "constant"
	LatticeOverdefined LatticeState = "overdefined"
)

type ConstantKind string

const (
	ConstantBool    ConstantKind = "bool"
	ConstantInteger ConstantKind = "integer"
	ConstantUnit    ConstantKind = "unit"
)

// Constant is an exact target-independent Oak value. Integer is canonical
// decimal: unsigned for uN and signed for iN.
type Constant struct {
	Kind    ConstantKind
	Type    Type
	Bool    bool
	Integer string
}

type SCCPValue struct {
	Value    ValueID
	State    LatticeState
	Constant Constant
}

// SCCPEdge identifies an executable control-flow edge. Arm is "branch",
// "true", or "false" and distinguishes two edges with the same target.
type SCCPEdge struct {
	From BlockID
	To   BlockID
	Arm  string
}

// SCCPBranch records a conditional whose exact direction is known.
type SCCPBranch struct {
	Block     BlockID
	Condition ValueID
	Taken     bool
	Target    BlockID
}

// SCCPResult is deterministic analysis evidence only. It does not rewrite the
// CFG and cannot authorize emission.
type SCCPResult struct {
	Values           []SCCPValue
	ExecutableBlocks []BlockID
	ExecutableEdges  []SCCPEdge
	Branches         []SCCPBranch
}

func (result SCCPResult) Value(id ValueID) (SCCPValue, bool) {
	index := sort.Search(len(result.Values), func(i int) bool { return result.Values[i].Value >= id })
	if index == len(result.Values) || result.Values[index].Value != id {
		return SCCPValue{}, false
	}
	return result.Values[index], true
}

type latticeValue struct {
	state    LatticeState
	constant Constant
}

type edgeKey struct {
	from BlockID
	to   BlockID
	arm  string
}

type incomingEdge struct {
	key       edgeKey
	arguments []ValueID
}

// AnalyzeSCCP discovers exact values and executable edges under Oak's
// fixed-width arithmetic. The input passes the independent CFG verifier and
// every known operation's arity and attributes are validated before analysis.
func AnalyzeSCCP(cfg CFG) (SCCPResult, error) {
	if err := Verify(cfg); err != nil {
		return SCCPResult{}, err
	}
	values := map[ValueID]latticeValue{}
	types := map[ValueID]Type{}
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	incoming := make(map[BlockID][]incomingEdge, len(cfg.Blocks))
	edgeCount := 0
	for i := range cfg.Blocks {
		block := &cfg.Blocks[i]
		blocks[block.ID] = block
		for _, parameter := range block.Parameters {
			values[parameter.ID] = latticeValue{state: LatticeUnknown}
			types[parameter.ID] = parameter.Type
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				values[result.ID] = latticeValue{state: LatticeUnknown}
				types[result.ID] = result.Type
			}
		}
		for _, edge := range namedEdges(block.Terminator) {
			key := edgeKey{from: block.ID, to: edge.edge.Target, arm: edge.arm}
			incoming[edge.edge.Target] = append(incoming[edge.edge.Target], incomingEdge{key: key, arguments: edge.edge.Arguments})
			edgeCount++
		}
	}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			if err := validateSCCPOperation(operation, types); err != nil {
				return SCCPResult{}, fmt.Errorf("optir: SCCP operation %s: %w", operation.Code, err)
			}
		}
	}

	executableBlocks := map[BlockID]bool{cfg.Entry: true}
	executableEdges := map[edgeKey]bool{}
	for _, parameter := range blocks[cfg.Entry].Parameters {
		values[parameter.ID] = latticeValue{state: LatticeOverdefined}
	}
	maximumIterations := 2*len(values) + edgeCount + len(blocks) + 1
	converged := false
	for iteration := 0; iteration < maximumIterations; iteration++ {
		changed := false
		for i := range cfg.Blocks {
			block := &cfg.Blocks[i]
			if !executableBlocks[block.ID] {
				continue
			}
			if block.ID != cfg.Entry {
				for parameterIndex, parameter := range block.Parameters {
					joined := latticeValue{state: LatticeUnknown}
					for _, edge := range incoming[block.ID] {
						if executableEdges[edge.key] {
							joined = joinLattice(joined, values[edge.arguments[parameterIndex]])
						}
					}
					changed = updateLattice(values, parameter.ID, joined) || changed
				}
			}
			for _, operation := range block.Operations {
				evaluated, err := evaluateSCCPOperation(operation, values)
				if err != nil {
					return SCCPResult{}, fmt.Errorf("optir: SCCP operation %s: %w", operation.Code, err)
				}
				for index, result := range operation.Results {
					changed = updateLattice(values, result.ID, evaluated[index]) || changed
				}
			}
			mark := func(edge Edge, arm string) {
				key := edgeKey{from: block.ID, to: edge.Target, arm: arm}
				if !executableEdges[key] {
					executableEdges[key] = true
					changed = true
				}
				if !executableBlocks[edge.Target] {
					executableBlocks[edge.Target] = true
					changed = true
				}
			}
			switch block.Terminator.Kind {
			case TerminatorBranch:
				mark(block.Terminator.True, "branch")
			case TerminatorCondBranch:
				condition := values[block.Terminator.Condition]
				switch condition.state {
				case LatticeConstant:
					if condition.constant.Kind != ConstantBool {
						return SCCPResult{}, fmt.Errorf("optir: SCCP condition %d is a non-Bool constant", block.Terminator.Condition)
					}
					if condition.constant.Bool {
						mark(block.Terminator.True, "true")
					} else {
						mark(block.Terminator.False, "false")
					}
				case LatticeOverdefined:
					mark(block.Terminator.True, "true")
					mark(block.Terminator.False, "false")
				}
			}
		}
		if !changed {
			converged = true
			break
		}
	}
	if !converged {
		return SCCPResult{}, fmt.Errorf("optir: SCCP did not converge within %d iterations", maximumIterations)
	}
	return buildSCCPResult(cfg, values, executableBlocks, executableEdges), nil
}

func updateLattice(values map[ValueID]latticeValue, id ValueID, next latticeValue) bool {
	current := values[id]
	joined := joinLattice(current, next)
	if equalLattice(current, joined) {
		return false
	}
	values[id] = joined
	return true
}

func joinLattice(left, right latticeValue) latticeValue {
	if left.state == LatticeUnknown {
		return right
	}
	if right.state == LatticeUnknown {
		return left
	}
	if left.state == LatticeOverdefined || right.state == LatticeOverdefined {
		return latticeValue{state: LatticeOverdefined}
	}
	if equalConstant(left.constant, right.constant) {
		return left
	}
	return latticeValue{state: LatticeOverdefined}
}

func equalLattice(left, right latticeValue) bool {
	return left.state == right.state && (left.state != LatticeConstant || equalConstant(left.constant, right.constant))
}

func equalConstant(left, right Constant) bool {
	return left.Kind == right.Kind && left.Type == right.Type && left.Bool == right.Bool && left.Integer == right.Integer
}

type namedEdge struct {
	arm  string
	edge Edge
}

func namedEdges(terminator Terminator) []namedEdge {
	switch terminator.Kind {
	case TerminatorBranch:
		return []namedEdge{{arm: "branch", edge: terminator.True}}
	case TerminatorCondBranch:
		return []namedEdge{{arm: "true", edge: terminator.True}, {arm: "false", edge: terminator.False}}
	default:
		return nil
	}
}

func validateSCCPOperation(operation Operation, types map[ValueID]Type) error {
	require := func(results, operands int) error {
		if len(operation.Results) != results || len(operation.Operands) != operands {
			return fmt.Errorf("has %d results/%d operands, want %d/%d", len(operation.Results), len(operation.Operands), results, operands)
		}
		return nil
	}
	switch operation.Code {
	case OpConstBool:
		if err := require(1, 0); err != nil {
			return err
		}
		value, err := uniqueAttribute(operation.Attributes, AttributeValue)
		if err != nil {
			return err
		}
		if value != "true" && value != "false" {
			return fmt.Errorf("has invalid Bool value %q", value)
		}
		if operation.Results[0].Type != TypeBool {
			return fmt.Errorf("has Bool constant result type %s", operation.Results[0].Type)
		}
	case OpConstInt:
		if err := require(1, 0); err != nil {
			return err
		}
		value, err := uniqueAttribute(operation.Attributes, AttributeValue)
		if err != nil {
			return err
		}
		if _, ok := new(big.Int).SetString(value, 10); !ok {
			return fmt.Errorf("has invalid integer value %q", value)
		}
		if _, _, ok := integerType(operation.Results[0].Type); !ok {
			return fmt.Errorf("has non-integer result type %s", operation.Results[0].Type)
		}
		normalized, err := normalizeInteger(value, operation.Results[0].Type)
		if err != nil || normalized != value {
			return fmt.Errorf("integer value %q is not canonical for %s", value, operation.Results[0].Type)
		}
	case OpConstUnit:
		if err := require(1, 0); err != nil {
			return err
		}
		if operation.Results[0].Type != Type("()") {
			return fmt.Errorf("has unit constant result type %s", operation.Results[0].Type)
		}
	case OpCopy:
		if err := require(1, 1); err != nil {
			return err
		}
		if types[operation.Operands[0]] != operation.Results[0].Type {
			return fmt.Errorf("copies %s into %s", types[operation.Operands[0]], operation.Results[0].Type)
		}
	case OpCastInt:
		if err := require(1, 1); err != nil {
			return err
		}
		if _, _, ok := integerType(types[operation.Operands[0]]); !ok {
			return fmt.Errorf("casts non-integer operand type %s", types[operation.Operands[0]])
		}
		if _, _, ok := integerType(operation.Results[0].Type); !ok {
			return fmt.Errorf("casts to non-integer result type %s", operation.Results[0].Type)
		}
		if !validIntegerWidening(types[operation.Operands[0]], operation.Results[0].Type) {
			return fmt.Errorf("cast from %s to %s is not value-preserving", types[operation.Operands[0]], operation.Results[0].Type)
		}
	case OpBoolNot:
		if err := require(1, 1); err != nil {
			return err
		}
		if types[operation.Operands[0]] != TypeBool || operation.Results[0].Type != TypeBool {
			return fmt.Errorf("requires Bool operand and result")
		}
	case OpIntNeg:
		if err := require(1, 1); err != nil {
			return err
		}
		if err := requireSameIntegerTypes(operation, types); err != nil {
			return err
		}
	case OpIntAdd, OpIntSub, OpIntMul, OpIntDiv, OpIntRem, OpIntAnd, OpIntOr, OpIntXor, OpIntShl, OpIntShr,
		OpLess, OpLessEqual, OpGreater, OpGreaterEqual:
		if err := require(1, 2); err != nil {
			return err
		}
		if operation.Code == OpLess || operation.Code == OpLessEqual || operation.Code == OpGreater || operation.Code == OpGreaterEqual {
			if operation.Results[0].Type != TypeBool || types[operation.Operands[0]] != types[operation.Operands[1]] {
				return fmt.Errorf("comparison operand/result types disagree")
			}
			if _, _, ok := integerType(types[operation.Operands[0]]); !ok {
				return fmt.Errorf("orders non-integer type %s", types[operation.Operands[0]])
			}
			return nil
		}
		return requireSameIntegerTypes(operation, types)
	case OpEqual, OpNotEqual:
		if err := require(1, 2); err != nil {
			return err
		}
		operandType := types[operation.Operands[0]]
		if operation.Results[0].Type != TypeBool || operandType != types[operation.Operands[1]] {
			return fmt.Errorf("equality operand/result types disagree")
		}
		if operandType != TypeBool {
			if _, _, ok := integerType(operandType); !ok {
				return fmt.Errorf("compares unsupported type %s", operandType)
			}
		}
	case OpLoadRegion:
		if err := require(1, 0); err != nil {
			return err
		}
		if operation.Results[0].Type != TypeBool {
			if _, _, ok := integerType(operation.Results[0].Type); !ok {
				return fmt.Errorf("loads unsupported type %s", operation.Results[0].Type)
			}
		}
		if len(operation.Effects) != 1 || operation.Effects[0] != EffectReadMemory {
			return fmt.Errorf("has effects %v, want exactly one memory-read effect", operation.Effects)
		}
	case OpStoreRegion:
		if err := require(0, 1); err != nil {
			return err
		}
		operandType := types[operation.Operands[0]]
		if operandType != TypeBool {
			if _, _, ok := integerType(operandType); !ok {
				return fmt.Errorf("stores unsupported type %s", operandType)
			}
		}
		if len(operation.Effects) != 1 || operation.Effects[0] != EffectWriteMemory {
			return fmt.Errorf("has effects %v, want exactly one memory-write effect", operation.Effects)
		}
	case OpCall:
		if len(operation.Results) != 1 {
			return fmt.Errorf("has %d results, want exactly one", len(operation.Results))
		}
		if len(operation.Effects) != 1 || operation.Effects[0] != EffectCall {
			return fmt.Errorf("has effects %v, want exactly one call effect", operation.Effects)
		}
		if len(operation.Attributes) != 1 {
			return fmt.Errorf("has %d attributes, want exactly one callee attribute", len(operation.Attributes))
		}
		_, err := uniqueAttribute(operation.Attributes, AttributeCallee)
		return err
	}
	return nil
}

func requireSameIntegerTypes(operation Operation, types map[ValueID]Type) error {
	resultType := operation.Results[0].Type
	if _, _, ok := integerType(resultType); !ok {
		return fmt.Errorf("has non-integer result type %s", resultType)
	}
	for _, operand := range operation.Operands {
		if types[operand] != resultType {
			return fmt.Errorf("operand type %s differs from result type %s", types[operand], resultType)
		}
	}
	return nil
}

func uniqueAttribute(attributes []Attribute, name string) (string, error) {
	value := ""
	found := false
	for _, attribute := range attributes {
		if attribute.Name != name {
			continue
		}
		if found {
			return "", fmt.Errorf("has duplicate %s attribute", name)
		}
		found = true
		value = attribute.Value
	}
	if !found || value == "" {
		return "", fmt.Errorf("has no %s attribute", name)
	}
	return value, nil
}

func evaluateSCCPOperation(operation Operation, values map[ValueID]latticeValue) ([]latticeValue, error) {
	unknown := func() []latticeValue {
		out := make([]latticeValue, len(operation.Results))
		for i := range out {
			out[i].state = LatticeUnknown
		}
		return out
	}
	overdefined := func() []latticeValue {
		out := make([]latticeValue, len(operation.Results))
		for i := range out {
			out[i].state = LatticeOverdefined
		}
		return out
	}
	constant := func(value Constant) []latticeValue {
		return []latticeValue{{state: LatticeConstant, constant: value}}
	}
	switch operation.Code {
	case OpConstBool:
		value, _ := uniqueAttribute(operation.Attributes, AttributeValue)
		return constant(Constant{Kind: ConstantBool, Type: operation.Results[0].Type, Bool: value == "true"}), nil
	case OpConstInt:
		value, _ := uniqueAttribute(operation.Attributes, AttributeValue)
		normalized, err := normalizeInteger(value, operation.Results[0].Type)
		if err != nil {
			return nil, err
		}
		return constant(Constant{Kind: ConstantInteger, Type: operation.Results[0].Type, Integer: normalized}), nil
	case OpConstUnit:
		return constant(Constant{Kind: ConstantUnit, Type: operation.Results[0].Type}), nil
	}
	operands := make([]latticeValue, len(operation.Operands))
	for i, operand := range operation.Operands {
		operands[i] = values[operand]
		if operands[i].state == LatticeOverdefined {
			return overdefined(), nil
		}
	}
	for _, operand := range operands {
		if operand.state == LatticeUnknown {
			return unknown(), nil
		}
	}
	if len(operation.Results) == 0 {
		return nil, nil
	}
	resultType := operation.Results[0].Type
	switch operation.Code {
	case OpCopy:
		copied := operands[0].constant
		if copied.Type != resultType {
			return overdefined(), nil
		}
		return constant(copied), nil
	case OpCastInt:
		if operands[0].constant.Kind != ConstantInteger {
			return overdefined(), nil
		}
		value, err := normalizeInteger(operands[0].constant.Integer, resultType)
		if err != nil {
			return overdefined(), nil
		}
		return constant(Constant{Kind: ConstantInteger, Type: resultType, Integer: value}), nil
	case OpBoolNot:
		if operands[0].constant.Kind != ConstantBool {
			return overdefined(), nil
		}
		return constant(Constant{Kind: ConstantBool, Type: resultType, Bool: !operands[0].constant.Bool}), nil
	case OpIntNeg:
		return evaluateIntegerUnary(operation.Code, operands[0].constant, resultType)
	case OpIntAdd, OpIntSub, OpIntMul, OpIntDiv, OpIntRem, OpIntAnd, OpIntOr, OpIntXor, OpIntShl, OpIntShr:
		return evaluateIntegerBinary(operation.Code, operands[0].constant, operands[1].constant, resultType)
	case OpEqual, OpNotEqual, OpLess, OpLessEqual, OpGreater, OpGreaterEqual:
		return evaluateComparison(operation.Code, operands[0].constant, operands[1].constant, resultType)
	default:
		return overdefined(), nil
	}
}

func evaluateIntegerUnary(code string, operand Constant, resultType Type) ([]latticeValue, error) {
	if operand.Kind != ConstantInteger {
		return []latticeValue{{state: LatticeOverdefined}}, nil
	}
	value, ok := new(big.Int).SetString(operand.Integer, 10)
	if !ok {
		return nil, fmt.Errorf("invalid constant integer %q", operand.Integer)
	}
	if code == OpIntNeg {
		value.Neg(value)
	}
	normalized, err := normalizeBigInteger(value, resultType)
	if err != nil {
		return []latticeValue{{state: LatticeOverdefined}}, nil
	}
	return []latticeValue{{state: LatticeConstant, constant: Constant{Kind: ConstantInteger, Type: resultType, Integer: normalized}}}, nil
}

func evaluateIntegerBinary(code string, left, right Constant, resultType Type) ([]latticeValue, error) {
	if left.Kind != ConstantInteger || right.Kind != ConstantInteger {
		return []latticeValue{{state: LatticeOverdefined}}, nil
	}
	l, lok := new(big.Int).SetString(left.Integer, 10)
	r, rok := new(big.Int).SetString(right.Integer, 10)
	if !lok || !rok {
		return nil, fmt.Errorf("invalid integer operand")
	}
	signed, bits, ok := integerType(resultType)
	if !ok {
		return []latticeValue{{state: LatticeOverdefined}}, nil
	}
	result := new(big.Int)
	switch code {
	case OpIntAdd:
		result.Add(l, r)
	case OpIntSub:
		result.Sub(l, r)
	case OpIntMul:
		result.Mul(l, r)
	case OpIntDiv, OpIntRem:
		if r.Sign() == 0 {
			return []latticeValue{{state: LatticeOverdefined}}, nil
		}
		if signed {
			minimum := new(big.Int).Neg(new(big.Int).Lsh(big.NewInt(1), uint(bits-1)))
			if l.Cmp(minimum) == 0 && r.Cmp(big.NewInt(-1)) == 0 {
				if code == OpIntDiv {
					result.Set(minimum)
				} else {
					result.SetInt64(0)
				}
			} else if code == OpIntDiv {
				result.Quo(l, r)
			} else {
				result.Rem(l, r)
			}
		} else {
			l = integerBits(l, bits)
			r = integerBits(r, bits)
			if code == OpIntDiv {
				result.Quo(l, r)
			} else {
				result.Rem(l, r)
			}
		}
	case OpIntAnd, OpIntOr, OpIntXor:
		l = integerBits(l, bits)
		r = integerBits(r, bits)
		switch code {
		case OpIntAnd:
			result.And(l, r)
		case OpIntOr:
			result.Or(l, r)
		default:
			result.Xor(l, r)
		}
	case OpIntShl, OpIntShr:
		countValue := integerBits(r, bits)
		if !countValue.IsUint64() || countValue.Uint64() >= uint64(bits) {
			return []latticeValue{{state: LatticeOverdefined}}, nil
		}
		l = integerBits(l, bits)
		if code == OpIntShl {
			result.Lsh(l, uint(countValue.Uint64()))
		} else {
			result.Rsh(l, uint(countValue.Uint64()))
		}
	}
	normalized, err := normalizeBigInteger(result, resultType)
	if err != nil {
		return []latticeValue{{state: LatticeOverdefined}}, nil
	}
	return []latticeValue{{state: LatticeConstant, constant: Constant{Kind: ConstantInteger, Type: resultType, Integer: normalized}}}, nil
}

func evaluateComparison(code string, left, right Constant, resultType Type) ([]latticeValue, error) {
	known := false
	comparison := 0
	if left.Kind == ConstantBool && right.Kind == ConstantBool {
		known = true
		if left.Bool != right.Bool {
			if !left.Bool {
				comparison = -1
			} else {
				comparison = 1
			}
		}
	} else if left.Kind == ConstantInteger && right.Kind == ConstantInteger && left.Type == right.Type {
		l, lok := new(big.Int).SetString(left.Integer, 10)
		r, rok := new(big.Int).SetString(right.Integer, 10)
		if lok && rok {
			known = true
			comparison = l.Cmp(r)
		}
	}
	if !known {
		return []latticeValue{{state: LatticeOverdefined}}, nil
	}
	var value bool
	switch code {
	case OpEqual:
		value = comparison == 0
	case OpNotEqual:
		value = comparison != 0
	case OpLess:
		value = comparison < 0
	case OpLessEqual:
		value = comparison <= 0
	case OpGreater:
		value = comparison > 0
	case OpGreaterEqual:
		value = comparison >= 0
	}
	return []latticeValue{{state: LatticeConstant, constant: Constant{Kind: ConstantBool, Type: resultType, Bool: value}}}, nil
}

func normalizeInteger(value string, typ Type) (string, error) {
	parsed, ok := new(big.Int).SetString(value, 10)
	if !ok {
		return "", fmt.Errorf("invalid integer %q", value)
	}
	return normalizeBigInteger(parsed, typ)
}

func normalizeBigInteger(value *big.Int, typ Type) (string, error) {
	signed, bits, ok := integerType(typ)
	if !ok {
		return "", fmt.Errorf("type %s is not a fixed-width integer", typ)
	}
	pattern := integerBits(value, bits)
	if signed && pattern.Bit(bits-1) == 1 {
		pattern.Sub(pattern, new(big.Int).Lsh(big.NewInt(1), uint(bits)))
	}
	return pattern.String(), nil
}

func integerBits(value *big.Int, bits int) *big.Int {
	modulus := new(big.Int).Lsh(big.NewInt(1), uint(bits))
	result := new(big.Int).Mod(new(big.Int).Set(value), modulus)
	if result.Sign() < 0 {
		result.Add(result, modulus)
	}
	return result
}

func integerType(typ Type) (signed bool, bits int, ok bool) {
	name := string(typ)
	if len(name) < 2 || (name[0] != 'i' && name[0] != 'u') {
		return false, 0, false
	}
	width, err := strconv.Atoi(name[1:])
	if err != nil || (width != 8 && width != 16 && width != 32 && width != 64 && width != 128) {
		return false, 0, false
	}
	return name[0] == 'i', width, true
}

func validIntegerWidening(source, target Type) bool {
	sourceSigned, sourceBits, sourceOK := integerType(source)
	targetSigned, targetBits, targetOK := integerType(target)
	if !sourceOK || !targetOK {
		return false
	}
	if sourceSigned == targetSigned {
		return sourceBits <= targetBits
	}
	return !sourceSigned && targetSigned && sourceBits < targetBits
}

func buildSCCPResult(cfg CFG, values map[ValueID]latticeValue, blocks map[BlockID]bool, edges map[edgeKey]bool) SCCPResult {
	result := SCCPResult{}
	ids := make([]int, 0, len(values))
	for id := range values {
		ids = append(ids, int(id))
	}
	sort.Ints(ids)
	for _, raw := range ids {
		id := ValueID(raw)
		value := values[id]
		result.Values = append(result.Values, SCCPValue{Value: id, State: value.state, Constant: value.constant})
	}
	for block := range blocks {
		if blocks[block] {
			result.ExecutableBlocks = append(result.ExecutableBlocks, block)
		}
	}
	sort.Slice(result.ExecutableBlocks, func(i, j int) bool { return result.ExecutableBlocks[i] < result.ExecutableBlocks[j] })
	for edge, executable := range edges {
		if executable {
			result.ExecutableEdges = append(result.ExecutableEdges, SCCPEdge{From: edge.from, To: edge.to, Arm: edge.arm})
		}
	}
	sort.Slice(result.ExecutableEdges, func(i, j int) bool {
		left, right := result.ExecutableEdges[i], result.ExecutableEdges[j]
		if left.From != right.From {
			return left.From < right.From
		}
		if left.To != right.To {
			return left.To < right.To
		}
		return left.Arm < right.Arm
	})
	for _, block := range cfg.Blocks {
		if !blocks[block.ID] || block.Terminator.Kind != TerminatorCondBranch {
			continue
		}
		condition := values[block.Terminator.Condition]
		if condition.state != LatticeConstant || condition.constant.Kind != ConstantBool {
			continue
		}
		branch := SCCPBranch{Block: block.ID, Condition: block.Terminator.Condition, Taken: condition.constant.Bool}
		if branch.Taken {
			branch.Target = block.Terminator.True.Target
		} else {
			branch.Target = block.Terminator.False.Target
		}
		result.Branches = append(result.Branches, branch)
	}
	sort.Slice(result.Branches, func(i, j int) bool { return result.Branches[i].Block < result.Branches[j].Block })
	return result
}

// String is useful in deterministic analysis snapshots.
func (constant Constant) String() string {
	switch constant.Kind {
	case ConstantBool:
		return strconv.FormatBool(constant.Bool)
	case ConstantInteger:
		return constant.Integer
	case ConstantUnit:
		return "()"
	}
	return strings.TrimSpace(string(constant.Kind))
}
