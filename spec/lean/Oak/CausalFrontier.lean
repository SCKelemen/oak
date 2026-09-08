namespace Oak.CausalFrontier

/-- A bounded causal frontier has one monotonically increasing counter per
    statically-known actor. `Fin n` makes out-of-range actor identities
    unrepresentable in the mathematical model. -/
abbrev Frontier (n : Nat) := Fin n -> Nat

/-- Pointwise causal domination. -/
def LE {n : Nat} (a b : Frontier n) : Prop :=
  ∀ i, a i ≤ b i

/-- The empty causal history. -/
def bottom (n : Nat) : Frontier n :=
  fun _ => 0

/-- Merge two causal histories. Join is pointwise maximum. -/
def join {n : Nat} (a b : Frontier n) : Frontier n :=
  fun i => max (a i) (b i)

/-- A received/event dot is already covered by a frontier when its sequence
    is at most the actor's frontier component. -/
def covers {n : Nat} (f : Frontier n) (actor : Fin n) (seq : Nat) : Prop :=
  seq ≤ f actor

@[simp] theorem join_apply {n : Nat} (a b : Frontier n) (i : Fin n) :
    join a b i = max (a i) (b i) := rfl

@[simp] theorem bottom_apply {n : Nat} (i : Fin n) :
    bottom n i = 0 := rfl

theorem le_refl {n : Nat} (a : Frontier n) : LE a a := by
  intro i
  exact Nat.le_refl _

theorem le_trans {n : Nat} {a b c : Frontier n} (hab : LE a b) (hbc : LE b c) : LE a c := by
  intro i
  exact Nat.le_trans (hab i) (hbc i)

theorem le_antisymm {n : Nat} {a b : Frontier n} (hab : LE a b) (hba : LE b a) : a = b := by
  funext i
  exact Nat.le_antisymm (hab i) (hba i)

theorem bottom_le {n : Nat} (a : Frontier n) : LE (bottom n) a := by
  intro i
  exact Nat.zero_le _

theorem le_join_left {n : Nat} (a b : Frontier n) : LE a (join a b) := by
  intro i
  exact Nat.le_max_left _ _

theorem le_join_right {n : Nat} (a b : Frontier n) : LE b (join a b) := by
  intro i
  exact Nat.le_max_right _ _

/-- `join` is the least upper bound, not merely some upper bound. -/
theorem join_least {n : Nat} {a b upper : Frontier n}
    (ha : LE a upper) (hb : LE b upper) : LE (join a b) upper := by
  intro i
  exact (Nat.max_le).2 ⟨ha i, hb i⟩

theorem join_idempotent {n : Nat} (a : Frontier n) : join a a = a := by
  funext i
  exact Nat.max_self _

theorem join_commutative {n : Nat} (a b : Frontier n) : join a b = join b a := by
  funext i
  exact Nat.max_comm _ _

theorem join_associative {n : Nat} (a b c : Frontier n) :
    join (join a b) c = join a (join b c) := by
  funext i
  exact Nat.max_assoc _ _ _

theorem join_bottom_left {n : Nat} (a : Frontier n) : join (bottom n) a = a := by
  funext i
  exact Nat.max_eq_right (Nat.zero_le _)

theorem join_bottom_right {n : Nat} (a : Frontier n) : join a (bottom n) = a := by
  funext i
  exact Nat.max_eq_left (Nat.zero_le _)

/-- Merge is monotone in both inputs. -/
theorem join_monotone {n : Nat} {a b c d : Frontier n}
    (hac : LE a c) (hbd : LE b d) : LE (join a b) (join c d) := by
  intro i
  apply (Nat.max_le).2
  constructor
  · exact Nat.le_trans (hac i) (Nat.le_max_left _ _)
  · exact Nat.le_trans (hbd i) (Nat.le_max_right _ _)

/-- Joining cannot forget any dot already covered by the left history. -/
theorem join_preserves_left_cover {n : Nat} {a b : Frontier n}
    {actor : Fin n} {seq : Nat} (h : covers a actor seq) :
    covers (join a b) actor seq := by
  exact Nat.le_trans h (Nat.le_max_left _ _)

/-- Joining cannot forget any dot already covered by the right history. -/
theorem join_preserves_right_cover {n : Nat} {a b : Frontier n}
    {actor : Fin n} {seq : Nat} (h : covers b actor seq) :
    covers (join a b) actor seq := by
  exact Nat.le_trans h (Nat.le_max_right _ _)

end Oak.CausalFrontier
