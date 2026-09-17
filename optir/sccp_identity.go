package optir

// evaluateSCCPIdentity recognizes only constant-result identities in the
// closed, total scalar vocabulary. AnalyzeSCCP has already checked every
// operand/result type: in particular, reflexive comparisons never see floats.
// Producers remain in the CFG; proving callResult*0 constant is not permission
// to delete the call, a memory read, or any trapping producer.
func evaluateSCCPIdentity(operation Operation, operands []latticeValue) (Constant, bool) {
	if len(operation.Results) != 1 || len(operation.Operands) != 2 || len(operands) != 2 || !canRewriteSCCPConstant(operation) {
		return Constant{}, false
	}
	resultType := operation.Results[0].Type
	zero := Constant{Kind: ConstantInteger, Type: resultType, Integer: "0"}
	if operation.Operands[0] == operation.Operands[1] {
		switch operation.Code {
		case OpIntSub, OpIntXor:
			return zero, true
		case OpEqual, OpLessEqual, OpGreaterEqual:
			return Constant{Kind: ConstantBool, Type: TypeBool, Bool: true}, true
		case OpNotEqual, OpLess, OpGreater:
			return Constant{Kind: ConstantBool, Type: TypeBool, Bool: false}, true
		}
	}
	switch operation.Code {
	case OpIntMul, OpIntAnd:
		for _, operand := range operands {
			if operand.state == LatticeConstant && operand.constant.Kind == ConstantInteger && operand.constant.Integer == "0" {
				return zero, true
			}
		}
	case OpIntOr:
		// Oak's canonical all-ones spelling is -1 for signed types and the
		// width's maximum integer for unsigned types, including u64.
		ones, err := normalizeInteger("-1", resultType)
		if err != nil {
			return Constant{}, false
		}
		for _, operand := range operands {
			if operand.state == LatticeConstant && operand.constant.Kind == ConstantInteger && operand.constant.Integer == ones {
				return Constant{Kind: ConstantInteger, Type: resultType, Integer: ones}, true
			}
		}
	}
	return Constant{}, false
}

func sccpAbsorbingOperation(operation Operation) bool {
	if len(operation.Results) != 1 || len(operation.Operands) != 2 || !canRewriteSCCPConstant(operation) {
		return false
	}
	switch operation.Code {
	case OpIntMul, OpIntAnd, OpIntOr:
		return true
	default:
		return false
	}
}
