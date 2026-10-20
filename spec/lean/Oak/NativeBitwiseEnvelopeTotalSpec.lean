import Oak.NativeBitwiseEnvelopeSpec

/-! Total native envelope result, independent of the extracted writer and its
word reads, loops, patch sequence, or returned result. -/
set_option autoImplicit false
namespace Oak.NativeBitwiseEnvelope
open Oak.MinimalELF (Machine)

def NameValid (name : Array UInt8) : Prop :=
  0 < name.size ∧ name.size ≤ 256 ∧ ∀ b ∈ name.toList, 0 < b ∧ b < 128

instance (name : Array UInt8) : Decidable (NameValid name) :=
  inferInstanceAs (Decidable (0 < name.size ∧ name.size ≤ 256 ∧
    ∀ b ∈ name.toList, 0 < b ∧ b < 128))

def bodyFromText (m : Machine) (text : Array UInt8) : Bytes :=
  text.toList.drop (Oak.NativeBitwiseImage.stubSize m)

def StartupValid (m : Machine) (text : Array UInt8) : Prop :=
  text.toList.take (Oak.NativeBitwiseImage.stubSize m) =
    Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m)

instance (m : Machine) (text : Array UInt8) : Decidable (StartupValid m text) :=
  inferInstanceAs (Decidable (text.toList.take (Oak.NativeBitwiseImage.stubSize m) =
    Oak.NativeBitwiseObject.toUInt8 (Oak.NativeBitwiseImage.startup m)))

def Capacity (m : Machine) (dst name : Array UInt8) : Prop :=
  Oak.NativeBitwiseImage.shOffset m (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 ≤ dst.size

instance (m : Machine) (dst name : Array UInt8) : Decidable (Capacity m dst name) :=
  inferInstanceAs (Decidable (Oak.NativeBitwiseImage.shOffset m
    (Oak.NativeBitwiseObject.fromUInt8 name.toList) + 384 ≤ dst.size))

/-- Natural length, actual byte prefix, and natural destination capacity. -/
def Eligible (m : Machine) (dst text name : Array UInt8) : Prop :=
  NameValid name ∧ text.size = Oak.NativeBitwiseImage.textSize m ∧
    StartupValid m text ∧ Capacity m dst name

instance (m : Machine) (dst text name : Array UInt8) : Decidable (Eligible m dst text name) :=
  inferInstanceAs (Decidable (NameValid name ∧ text.size = Oak.NativeBitwiseImage.textSize m ∧
    StartupValid m text ∧ Capacity m dst name))

/-- Success is independent field concatenation followed by the original suffix. -/
def envelopeSuccess (m : Machine) (dst text name : Array UInt8) : UInt32 × Array UInt8 :=
  let bytes := E m name.toList (bodyFromText m text)
  (UInt32.ofNat bytes.length, (bytes ++ dst.toList.drop bytes.length).toArray)

/-- Total result over all architecture tags and arrays. The refinement theorem
requires representable array sizes; it makes no valid-input assumption. -/
def envelopeResult (dst text : Array UInt8) (arch : UInt32) (name : Array UInt8) : UInt32 × Array UInt8 :=
  if arch = 1 then
    if Eligible .arm64 dst text name then envelopeSuccess .arm64 dst text name else (0, dst)
  else if arch = 2 then
    if Eligible .rv64 dst text name then envelopeSuccess .rv64 dst text name else (0, dst)
  else (0, dst)

end Oak.NativeBitwiseEnvelope
