/-!
# Protocol lowering: payload classes

`Oak.Protocol` proves the transition table computes a declaration's
first-match semantics over abstract symbols. A mixed-symbol machine
(docs/spec/112-protocols.md section 2a) has steps whose guards read a
payload value; the compiler makes one symbol per *class* of payload
values, where two values are in the same class exactly when every guard
of the step decides them alike, and fills the table row from one
representative per class. This file proves that step sound: the
first line that fires from a state depends on the payload only through
the vector of guard outcomes, so the representative's target is every
member's target.

The model here is one step's lines with guards over `V` payload values;
the symbol-level facts (sentinel, sink, batch run) are `Oak.Protocol`'s.
-/

namespace Oak.Protocol.Classes

/-- One guarded line of a step: from a source state, when the guard holds
of the payload, to a target. -/
structure GLine (S V : Nat) where
  from_ : Fin S
  guard : Fin V → Bool
  to    : Fin S

variable {S V : Nat}

/-- The declared semantics over payload values: the first line from this
state whose guard holds gives the target. -/
def nextV (ls : List (GLine S V)) (s : Fin S) (v : Fin V) : Option (Fin S) :=
  (ls.find? fun l => l.from_ == s && l.guard v).map (·.to)

/-- The vector of guard outcomes of a payload value, over the step's lines
in declaration order — the compiler's class key. -/
def outcomes (ls : List (GLine S V)) (v : Fin V) : List Bool :=
  ls.map fun l => l.guard v

theorem nextV_nil (s : Fin S) (v : Fin V) : nextV ([] : List (GLine S V)) s v = none := rfl

theorem nextV_cons (l : GLine S V) (ls : List (GLine S V)) (s : Fin S) (v : Fin V) :
    nextV (l :: ls) s v = if l.from_ == s && l.guard v then some l.to else nextV ls s v := by
  unfold nextV
  rw [List.find?_cons]
  cases h : (l.from_ == s && l.guard v) <;> simp

/-- Two payload values with the same guard outcomes take the same first
line from every state. -/
theorem nextV_congr (ls : List (GLine S V)) (s : Fin S) (v w : Fin V)
    (h : outcomes ls v = outcomes ls w) : nextV ls s v = nextV ls s w := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [outcomes, List.map, List.cons.injEq] at h
    rw [nextV_cons, nextV_cons, h.1, ih h.2]

/-- The compiler's classing of a step: `cls` sends a payload value to its
class, `rep` picks the representative the table row is filled from, and
the two facts the construction guarantees — the representative of a class
is in that class (it is the first value seen with the class's outcome
vector), and values in one class have the same outcomes (the class *is*
the outcome vector). -/
structure Classing (ls : List (GLine S V)) (C : Nat) where
  cls : Fin V → Fin C
  rep : Fin C → Fin V
  rep_cls : ∀ c, cls (rep c) = c
  faithful : ∀ v w, cls v = cls w → outcomes ls v = outcomes ls w

/-- The table row built from representatives computes the declared
step for every payload value: `table[state][base + cls v]` is `nextV s v`. -/
theorem lowering_correct {C : Nat} (ls : List (GLine S V)) (k : Classing ls C)
    (s : Fin S) (v : Fin V) : nextV ls s (k.rep (k.cls v)) = nextV ls s v :=
  nextV_congr ls s _ _ (k.faithful _ _ (k.rep_cls (k.cls v)))

/-- Legality likewise depends on the payload only through its class. -/
theorem legal_correct {C : Nat} (ls : List (GLine S V)) (k : Classing ls C)
    (s : Fin S) (v : Fin V) :
    (nextV ls s (k.rep (k.cls v))).isSome = (nextV ls s v).isSome := by
  rw [lowering_correct]

end Oak.Protocol.Classes
