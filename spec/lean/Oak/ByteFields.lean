/-! Shared byte-list field splitting, available on both supported Lean versions.
The Lean4.33 compatibility theorem checks the old library implementation exactly. -/
set_option autoImplicit false
namespace Oak.ByteFields

def splitPrepend (p : UInt8 → Bool) : List UInt8 → List UInt8 → List (List UInt8)
  | [], acc => [acc.reverse]
  | a :: rest, acc =>
      if p a then acc.reverse :: splitPrepend p rest [] else splitPrepend p rest (a :: acc)

def splitOn (source : List UInt8) (separator : UInt8) : List (List UInt8) :=
  splitPrepend (fun byte => byte == separator) source []

end Oak.ByteFields
