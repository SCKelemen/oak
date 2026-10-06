import Std

/-! Checked placement for the Oak text/data linker and a concrete byte-patch
transaction model. The arithmetic is unbounded; successful admission proves
that returned offsets/addresses fit their machine representations. Executable
correspondence checks bind the placement decisions to compiled Oak. This is
not a universal refinement proof of the compiler or complete object linker. -/
namespace Oak.LinkerLayout

def padding (base cursor alignment : Nat) : Nat :=
  (alignment - ((base % alignment + cursor % alignment) % alignment)) % alignment

def place (base cursor size alignment capacity : Nat) : Option (Nat × Nat) :=
  let start := cursor + padding base cursor alignment
  let stop := start + size
  if base < 2^64 ∧ cursor < 2^32 ∧ size < 2^32 ∧ capacity < 2^32 ∧
      0 < size ∧ 0 < alignment ∧ alignment ≤ 4096 ∧
      Nat.land alignment (alignment - 1) = 0 ∧
      stop ≤ capacity ∧ base + stop < 2^64 then some (start, stop)
  else none

theorem padding_lt {base cursor alignment : Nat} (h : 0 < alignment) :
    padding base cursor alignment < alignment := by
  exact Nat.mod_lt _ h

theorem padding_aligned {base cursor alignment : Nat} (h : 0 < alignment) :
    (base + (cursor + padding base cursor alignment)) % alignment = 0 := by
  have hr := Nat.mod_lt (base + cursor) h
  have hp : padding base cursor alignment =
      (alignment - (base + cursor) % alignment) % alignment := by
    simp [padding, Nat.add_mod]
  rw [hp, ← Nat.add_assoc, Nat.add_mod]
  by_cases hz : (base + cursor) % alignment = 0
  · simp [hz]
  · have hs : alignment - (base + cursor) % alignment < alignment := by omega
    simp only [Nat.mod_eq_of_lt hs]
    have he : (base + cursor) % alignment +
        (alignment - (base + cursor) % alignment) = alignment := by omega
    rw [he, Nat.mod_self]

theorem padding_minimal {base cursor alignment candidate : Nat}
    (ha : 0 < alignment) (hc : cursor ≤ candidate)
    (halign : (base + candidate) % alignment = 0) :
    cursor + padding base cursor alignment ≤ candidate := by
  have hr := Nat.mod_lt (base + cursor) ha
  have hp : padding base cursor alignment =
      (alignment - (base + cursor) % alignment) % alignment := by
    simp [padding, Nat.add_mod]
  by_cases hz : (base + cursor) % alignment = 0
  · simpa [hp, hz] using hc
  · have hs : alignment - (base + cursor) % alignment < alignment := by omega
    simp only [Nat.mod_eq_of_lt hs] at hp
    by_cases hn : cursor + padding base cursor alignment ≤ candidate
    · exact hn
    have hd : candidate - cursor < alignment := by omega
    have hsum : (base + cursor) % alignment + (candidate - cursor) < alignment := by omega
    have he : base + candidate = (base + cursor) + (candidate - cursor) := by omega
    rw [he, Nat.add_mod, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hsum] at halign
    omega

theorem place_spec {base cursor size alignment capacity start stop : Nat}
    (h : place base cursor size alignment capacity = some (start, stop)) :
    cursor ≤ start ∧ start < stop ∧ stop = start + size ∧
    stop ≤ capacity ∧ capacity < 2^32 ∧ base + stop < 2^64 ∧
    (base + start) % alignment = 0 ∧ start - cursor < alignment := by
  unfold place at h
  dsimp only at h
  split at h
  · rename_i admitted
    have pair := Option.some.inj h
    have hstart := congrArg Prod.fst pair
    have hstop := congrArg Prod.snd pair
    simp only at hstart hstop
    have ha : 0 < alignment := admitted.2.2.2.2.2.1
    have hp := padding_lt (base := base) (cursor := cursor) ha
    have halign := padding_aligned (base := base) (cursor := cursor) ha
    rcases admitted with ⟨_, _, _, hc, hs, _, _, _, he, hb⟩
    constructor; · omega
    constructor; · omega
    constructor; · omega
    constructor; · omega
    constructor; · exact hc
    constructor; · omega
    constructor
    · simpa [hstart] using halign
    · omega
  · simp at h

theorem consecutive_disjoint {base cursor size alignment capacity start stop
    nextSize nextAlignment nextStart nextStop : Nat}
    (h : place base cursor size alignment capacity = some (start, stop))
    (hn : place base stop nextSize nextAlignment capacity = some (nextStart, nextStop)) :
    start + size ≤ nextStart := by
  have hp := place_spec h
  have hnp := place_spec hn
  omega

theorem placement_intermediate_fits {base cursor size alignment : Nat}
    (hc : cursor < 2^32) (hs : size < 2^32)
    (ha : 0 < alignment) (hb : alignment ≤ 4096) :
    cursor + padding base cursor alignment + size < 2^64 := by
  have hp := padding_lt (base := base) (cursor := cursor) ha
  omega

theorem symbol_address_inside {base cursor size alignment capacity start stop offset : Nat}
    (h : place base cursor size alignment capacity = some (start, stop))
    (ho : offset < size) :
    start + offset < capacity ∧ base + (start + offset) < 2^64 := by
  have hp := place_spec h
  omega

/-! A byte plan is committed only after the entire ordered plan is admitted.
The byte store is total; the explicit length models its owned valid extent. -/
structure Write where
  offset : Nat
  value : UInt8
  deriving Repr, DecidableEq

def validWrites (size last : Nat) : List Write → Bool
  | [] => true
  | w :: rest => decide (last ≤ w.offset ∧ w.offset < size) &&
      validWrites size (w.offset + 1) rest

def applyWrites (bytes : Nat → UInt8) : List Write → Nat → UInt8
  | [] => bytes
  | w :: rest => applyWrites (fun i => if i = w.offset then w.value else bytes i) rest

def transact (size : Nat) (bytes : Nat → UInt8) (writes : List Write) :
    Bool × (Nat → UInt8) :=
  if validWrites size 0 writes then (true, applyWrites bytes writes) else (false, bytes)

theorem rejected_preserves {size : Nat} {bytes : Nat → UInt8} {writes : List Write}
    (h : (transact size bytes writes).1 = false) :
    (transact size bytes writes).2 = bytes := by
  unfold transact at *
  split at * <;> simp_all

theorem validWrites_member {size last : Nat} {writes : List Write}
    (h : validWrites size last writes = true) {w : Write} (hw : w ∈ writes) :
    w.offset < size := by
  induction writes generalizing last with
  | nil => simp at hw
  | cons first rest ih =>
    simp only [validWrites, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hw with he | ht
    · subst w; exact h.1.2
    · exact ih h.2 ht

theorem invalid_late_write {size : Nat} {bytes : Nat → UInt8} {writes : List Write}
    {w : Write} (hw : w ∈ writes) (ho : size ≤ w.offset) :
    transact size bytes writes = (false, bytes) := by
  have hv : validWrites size 0 writes = false := by
    cases h : validWrites size 0 writes with
    | false => rfl
    | true => have hb := validWrites_member h hw; omega
  simp [transact, hv]

theorem applyWrites_frame {size last : Nat} {bytes : Nat → UInt8} {writes : List Write}
    (h : validWrites size last writes = true) {i : Nat} (hi : size ≤ i) :
    applyWrites bytes writes i = bytes i := by
  induction writes generalizing last bytes with
  | nil => rfl
  | cons w rest ih =>
    simp only [validWrites, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [applyWrites]
    rw [ih h.2]
    have hn : i ≠ w.offset := by omega
    simp [hn]

theorem transaction_frame (size : Nat) (bytes : Nat → UInt8) (writes : List Write)
    (i : Nat) (hi : size ≤ i) : (transact size bytes writes).2 i = bytes i := by
  unfold transact
  split
  · rename_i h
    exact applyWrites_frame h hi
  · rfl

end Oak.LinkerLayout
