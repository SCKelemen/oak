package optir

// Stable target-independent operation names. Backends may select many machine
// implementations for one operation; these names describe Oak semantics, not
// an instruction set.
const (
	OpConstBool = "const.bool"
	OpConstInt  = "const.integer"
	OpConstUnit = "const.unit"
	OpCopy      = "copy"
	// OpCastInt is Oak's value-preserving primitive constructor widening,
	// including an unsigned value into a strictly wider signed carrier. It is
	// never a truncating or saturating conversion.
	OpCastInt = "integer.cast"

	OpBoolNot = "bool.not"
	OpIntNeg  = "integer.neg"
	OpIntAdd  = "integer.add"
	OpIntSub  = "integer.sub"
	OpIntMul  = "integer.mul"
	OpIntDiv  = "integer.div"
	OpIntRem  = "integer.rem"
	OpIntAnd  = "integer.and"
	OpIntOr   = "integer.or"
	OpIntXor  = "integer.xor"
	OpIntShl  = "integer.shl"
	OpIntShr  = "integer.shr"

	OpEqual        = "compare.equal"
	OpNotEqual     = "compare.not-equal"
	OpLess         = "compare.less"
	OpLessEqual    = "compare.less-equal"
	OpGreater      = "compare.greater"
	OpGreaterEqual = "compare.greater-equal"

	OpCall = "call"
)

const (
	AttributeValue  = "value"
	AttributeCallee = "callee"
)
