import Oak.BitwiseSource
set_option autoImplicit false
namespace Oak.ByteFields

theorem splitPrepend_library (p : UInt8 → Bool) (source acc : List UInt8) :
    splitPrepend p source acc = List.splitOnPPrepend p source acc := by
  induction source generalizing acc with
  | nil => rfl
  | cons b rest ih =>
      simp only [splitPrepend, List.splitOnPPrepend]
      split <;> simp only [ih]

/-- The shared implementation preserves the original source-checker splitting
on every possible byte input, including repeated/leading/trailing separators. -/
theorem splitOn_library (source : List UInt8) (separator : UInt8) :
    splitOn source separator = source.splitOn separator := by
  exact splitPrepend_library _ _ _

end Oak.ByteFields
