import Oak.HappensBefore

namespace Oak.SequentialConsistency

universe u

/-- A strict total order restricted to events classified as seq-cst. The
    executable witness represents this relation by position in a caller-owned
    list; this abstract form states the mathematical contract. -/
structure SCOrder {Event : Type u} (isSC : Event -> Prop) where
  before : Event -> Event -> Prop
  irreflexive : ∀ event, ¬ before event event
  transitive : ∀ {a b c}, before a b -> before b c -> before a c
  total : ∀ {a b}, isSC a -> isSC b -> a ≠ b -> before a b ∨ before b a

/-- The global SC order must preserve happens-before between seq-cst events. -/
def ConsistentWithHB {Event : Type u} {isSC : Event -> Prop}
    (order : SCOrder isSC) (hb : Event -> Event -> Prop) : Prop :=
  ∀ {a b}, isSC a -> isSC b -> hb a b -> order.before a b

/-- The global SC order must preserve per-location modification order between
    seq-cst writes/RMWs. -/
def ConsistentWithModification {Event : Type u} {isSC : Event -> Prop}
    (order : SCOrder isSC)
    (isSCWrite : Event -> Prop)
    (modificationBefore : Event -> Event -> Prop) : Prop :=
  ∀ {a b}, isSCWrite a -> isSCWrite b ->
    modificationBefore a b -> order.before a b

/-- An SC read that observes `source` may not skip a later modification already
    visible before the read through happens-before or through SC order. If the
    source itself is SC, it must precede the read in SC order. -/
def VisibleSource {Event : Type u} {isSC : Event -> Prop}
    (order : SCOrder isSC)
    (hb modificationBefore : Event -> Event -> Prop)
    (isWrite : Event -> Prop)
    (source read : Event) : Prop :=
  (isSC source -> order.before source read) ∧
  ∀ later, isWrite later -> modificationBefore source later ->
    (¬ hb later read) ∧ ¬ (isSC later ∧ order.before later read)

/-- Reading the implicit initialized value is allowed only when no represented
    write is already visible before the SC read through HB or SC order. -/
def InitialValueAllowed {Event : Type u} {isSC : Event -> Prop}
    (order : SCOrder isSC)
    (hb : Event -> Event -> Prop)
    (isWrite : Event -> Prop)
    (read : Event) : Prop :=
  ∀ write, isWrite write ->
    (¬ hb write read) ∧ ¬ (isSC write ∧ order.before write read)

/-- If SC order respects HB, an HB edge between SC events can never be reversed
    in SC order. -/
theorem hb_consistency_excludes_reverse
    {Event : Type u} {isSC : Event -> Prop}
    {order : SCOrder isSC} {hb : Event -> Event -> Prop}
    {a b : Event}
    (hConsistent : ConsistentWithHB order hb)
    (hA : isSC a) (hB : isSC b)
    (hHB : hb a b) :
    ¬ order.before b a := by
  intro hReverse
  have hForward : order.before a b := hConsistent hA hB hHB
  have hCycle : order.before a a := order.transitive hForward hReverse
  exact order.irreflexive a hCycle

/-- Likewise, SC order cannot reverse modification order between SC writes. -/
theorem modification_consistency_excludes_reverse
    {Event : Type u} {isSC : Event -> Prop}
    {order : SCOrder isSC}
    {isSCWrite : Event -> Prop}
    {modificationBefore : Event -> Event -> Prop}
    {a b : Event}
    (hConsistent : ConsistentWithModification order isSCWrite modificationBefore)
    (hA : isSCWrite a) (hB : isSCWrite b)
    (hMO : modificationBefore a b) :
    ¬ order.before b a := by
  intro hReverse
  have hForward : order.before a b := hConsistent hA hB hMO
  have hCycle : order.before a a := order.transitive hForward hReverse
  exact order.irreflexive a hCycle

/-- A source visibility witness directly excludes skipping any later write that
    happens-before the SC read. -/
theorem visible_source_does_not_skip_hb_write
    {Event : Type u} {isSC : Event -> Prop}
    {order : SCOrder isSC}
    {hb modificationBefore : Event -> Event -> Prop}
    {isWrite : Event -> Prop}
    {source read later : Event}
    (hVisible : VisibleSource order hb modificationBefore isWrite source read)
    (hWrite : isWrite later)
    (hLater : modificationBefore source later) :
    ¬ hb later read := by
  exact (hVisible.2 later hWrite hLater).1

/-- Nor can it skip a later seq-cst write already SC-before the read. -/
theorem visible_source_does_not_skip_sc_write
    {Event : Type u} {isSC : Event -> Prop}
    {order : SCOrder isSC}
    {hb modificationBefore : Event -> Event -> Prop}
    {isWrite : Event -> Prop}
    {source read later : Event}
    (hVisible : VisibleSource order hb modificationBefore isWrite source read)
    (hWrite : isWrite later)
    (hLater : modificationBefore source later)
    (hSC : isSC later) :
    ¬ order.before later read := by
  intro hBefore
  exact (hVisible.2 later hWrite hLater).2 ⟨hSC, hBefore⟩

/-- If an SC source is observed, the source must be globally SC-before the read. -/
theorem sc_source_precedes_sc_read
    {Event : Type u} {isSC : Event -> Prop}
    {order : SCOrder isSC}
    {hb modificationBefore : Event -> Event -> Prop}
    {isWrite : Event -> Prop}
    {source read : Event}
    (hVisible : VisibleSource order hb modificationBefore isWrite source read)
    (hSourceSC : isSC source) :
    order.before source read :=
  hVisible.1 hSourceSC

/-- An SC read of the implicit initial value cannot have an SC write before it. -/
theorem initial_value_excludes_prior_sc_write
    {Event : Type u} {isSC : Event -> Prop}
    {order : SCOrder isSC}
    {hb : Event -> Event -> Prop}
    {isWrite : Event -> Prop}
    {write read : Event}
    (hInitial : InitialValueAllowed order hb isWrite read)
    (hWrite : isWrite write)
    (hSC : isSC write) :
    ¬ order.before write read := by
  intro hBefore
  exact (hInitial write hWrite).2 ⟨hSC, hBefore⟩

end Oak.SequentialConsistency
