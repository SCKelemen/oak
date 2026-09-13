/-!
# The Teddy prefilter is sound

`benchmarks/scanning/literals.oak` scans a byte stream for a set of
literals the way Hyperscan's Teddy does: literals are hashed into eight
buckets; for each of the first three bytes of every literal the compiler
builds a low-nibble table and a high-nibble table of bucket masks; at a
position, the AND of the six lookups over the three bytes there is the
candidate mask, and a literal is compared against the input only at
positions where its bucket's bit is set.

This file proves the prefilter sound: a literal that occurs at a position
has its bucket's bit set in the candidate mask there. So verifying at
candidate lanes finds every occurrence, and the count is exact — the
verification never counts anything that is not an occurrence, and no
occurrence is outside the candidates.

The model is at the level of the table *predicates*: bucket `b` is set in
table `k` at nibble `n` exactly when some literal of bucket `b` has that
nibble at byte `k`, which is what the compiler's OR loop over the literals
builds; the AND of masks has bit `b` set exactly when every operand has,
which is the conjunction below.
-/

namespace Oak.Teddy

/-- A literal set: `L` literals, each at least three bytes, each in a bucket. -/
structure LitSet (L : Nat) where
  lit  : Fin L → List UInt8
  bkt  : Fin L → Fin 8
  long : ∀ i, 3 ≤ (lit i).length

/-- The byte at a position, zero past the end (the harness zero-pads). -/
def byteAt (t : List UInt8) (p : Nat) : UInt8 := t.getD p 0

def lowNib (b : UInt8) : UInt8 := b &&& 15
def highNib (b : UInt8) : UInt8 := b >>> 4

variable {L : Nat}

/-- Table `k`, low nibbles: bucket `b` is set at nibble `n` when some literal
in bucket `b` has low nibble `n` at byte `k`. -/
def lo (s : LitSet L) (k : Nat) (n : UInt8) (b : Fin 8) : Prop :=
  ∃ i, s.bkt i = b ∧ lowNib (byteAt (s.lit i) k) = n

/-- Table `k`, high nibbles. -/
def hi (s : LitSet L) (k : Nat) (n : UInt8) (b : Fin 8) : Prop :=
  ∃ i, s.bkt i = b ∧ highNib (byteAt (s.lit i) k) = n

/-- One byte's lookup: both nibble tables set for the bucket. -/
def lookup (s : LitSet L) (k : Nat) (c : UInt8) (b : Fin 8) : Prop :=
  lo s k (lowNib c) b ∧ hi s k (highNib c) b

/-- The candidate mask at position `p`: the three lookups over the bytes at
`p`, `p + 1`, `p + 2` all set for the bucket. -/
def cand (s : LitSet L) (t : List UInt8) (p : Nat) (b : Fin 8) : Prop :=
  lookup s 0 (byteAt t p) b ∧ lookup s 1 (byteAt t (p + 1)) b ∧ lookup s 2 (byteAt t (p + 2)) b

/-- A literal occurs at `p` when the input there begins with it. -/
def occursAt (lit t : List UInt8) (p : Nat) : Prop :=
  (t.drop p).take lit.length = lit

theorem byteAt_of_occurs {lit t : List UInt8} {p : Nat} (h : occursAt lit t p)
    (k : Nat) (hk : k < lit.length) : byteAt t (p + k) = byteAt lit k := by
  unfold occursAt at h
  unfold byteAt
  rw [← h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-- The literal's own byte passes its own lookup. -/
theorem lookup_self (s : LitSet L) (i : Fin L) (k : Nat) :
    lookup s k (byteAt (s.lit i) k) (s.bkt i) :=
  ⟨⟨i, rfl, rfl⟩, ⟨i, rfl, rfl⟩⟩

/-- **Soundness**: a literal occurring at `p` sets its bucket's bit in the
candidate mask at `p`. -/
theorem sound (s : LitSet L) (t : List UInt8) (p : Nat) (i : Fin L)
    (h : occursAt (s.lit i) t p) : cand s t p (s.bkt i) := by
  have l := s.long i
  refine ⟨?_, ?_, ?_⟩
  · rw [show p = p + 0 from rfl, byteAt_of_occurs h 0 (by omega)]; exact lookup_self s i 0
  · rw [byteAt_of_occurs h 1 (by omega)]; exact lookup_self s i 1
  · rw [byteAt_of_occurs h 2 (by omega)]; exact lookup_self s i 2

/-- **Exactness**: verifying literal `i` only where its bucket is a candidate
finds exactly its occurrences. -/
theorem exact (s : LitSet L) (t : List UInt8) (p : Nat) (i : Fin L) :
    (cand s t p (s.bkt i) ∧ occursAt (s.lit i) t p) ↔ occursAt (s.lit i) t p :=
  ⟨fun h => h.2, fun h => ⟨sound s t p i h, h⟩⟩

end Oak.Teddy
