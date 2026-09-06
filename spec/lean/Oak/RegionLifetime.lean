namespace Oak.RegionLifetime

/-- A half-open lifetime interval [start, finish). -/
structure Lifetime where
  start : Nat
  finish : Nat
  deriving DecidableEq, Repr

/-- A lifetime is internally consistent when its start does not follow its end. -/
def WellFormed (lifetime : Lifetime) : Prop :=
  lifetime.start ≤ lifetime.finish

/-- `child` is wholly contained within `parent`. This is the abstract region
    relation used for values tied to arena/region identity R. -/
def Within (child parent : Lifetime) : Prop :=
  parent.start ≤ child.start ∧ child.finish ≤ parent.finish

/-- A value/region is alive at an instant when the instant lies in its
    half-open lifetime interval. -/
def AliveAt (lifetime : Lifetime) (instant : Nat) : Prop :=
  lifetime.start ≤ instant ∧ instant < lifetime.finish

theorem within_refl (lifetime : Lifetime) :
    Within lifetime lifetime := by
  constructor <;> exact Nat.le_refl _

theorem within_trans (inner middle outer : Lifetime)
    (him : Within inner middle) (hmo : Within middle outer) :
    Within inner outer := by
  constructor
  · exact Nat.le_trans hmo.1 him.1
  · exact Nat.le_trans him.2 hmo.2

/-- If a region-bound value is alive, the region containing it must also be
    alive at the same instant. -/
theorem within_preserves_alive (value region : Lifetime) (instant : Nat)
    (hwithin : Within value region) (hvalue : AliveAt value instant) :
    AliveAt region instant := by
  constructor
  · exact Nat.le_trans hwithin.1 hvalue.1
  · exact Nat.lt_of_lt_of_le hvalue.2 hwithin.2

/-- Once the containing region has ended, a region-bound value cannot remain
    alive. This is the abstract non-escape law for T[R]. -/
theorem no_escape_after_region_finish (value region : Lifetime) (instant : Nat)
    (hwithin : Within value region) (hended : region.finish ≤ instant) :
    ¬ AliveAt value instant := by
  intro hvalue
  have hregion := within_preserves_alive value region instant hwithin hvalue
  exact (Nat.not_lt_of_ge hended) hregion.2

/-- A value cannot begin before the region to which it is bound. -/
theorem no_escape_before_region_start (value region : Lifetime)
    (hwithin : Within value region) :
    region.start ≤ value.start := by
  exact hwithin.1

/-- A value cannot finish after the region to which it is bound. -/
theorem value_finishes_within_region (value region : Lifetime)
    (hwithin : Within value region) :
    value.finish ≤ region.finish := by
  exact hwithin.2

/-- Nested region/value containment composes: if a value is within an inner
    region and the inner region is within an outer region, the value is also
    within the outer region. -/
theorem nested_region_non_escape (value inner outer : Lifetime)
    (hvalue : Within value inner) (hinner : Within inner outer) :
    Within value outer := by
  exact within_trans value inner outer hvalue hinner

/-- A live interval necessarily has positive extent. -/
theorem alive_implies_start_before_finish (lifetime : Lifetime) (instant : Nat)
    (halive : AliveAt lifetime instant) :
    lifetime.start < lifetime.finish := by
  exact Nat.lt_of_le_of_lt halive.1 halive.2

end Oak.RegionLifetime
