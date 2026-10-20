import Oak.Stdlib.TimeOffsetTextLaws
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def offset_magnitude (z : OffsetDateTime) : UInt32 :=
  (if z.offset_minutes < 0 then 0-z.offset_minutes else z.offset_minutes).toUInt32

def offset_negative (z : OffsetDateTime) : Bool :=
  decide (z.offset_minutes < 0) || (match z.offset_kind with | .UnknownLocal => true | _ => false)

theorem offset_valid_fields (z : OffsetDateTime) (fuel : Nat)
    (hv : offset_datetime_valid z fuel = some true) :
    datetime_valid z.datetime fuel = some true ∧
    -1440 < z.offset_minutes ∧ z.offset_minutes < 1440 ∧
    (match z.offset_kind with | .Numeric => True | _ => z.offset_minutes = 0) := by
  simp only [offset_datetime_valid, bind, pure, Option.bind_eq_some_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  have hb' : b = (decide (z.offset_minutes > (0-1440)) && decide (z.offset_minutes < 1440)) := by
    simpa [offset_valid] using hb.symm
  subst b
  cases a <;> cases hk : z.offset_kind <;> simp [hk] at hab
  all_goals exact ⟨ha, by simpa [and_assoc] using hab⟩

theorem numeric_offset_reconstruct (off : Int32) (hl : -1440 < off) (hh : off < 1440) :
    let mag := (if off < 0 then 0-off else off).toUInt32
    mag / 60 < 24 ∧ mag % 60 < 60 ∧
    numeric_offset_value (mag/60) (mag%60) (decide (off < 0)) = off ∧
    numeric_offset_kind (mag/60) (mag%60) (decide (off < 0)) = .Numeric := by
  simp only [numeric_offset_value, numeric_offset_kind]
  bv_decide

end Oak.Stdlib.Time
