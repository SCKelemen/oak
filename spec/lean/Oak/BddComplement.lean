/-!
# Complement edges in the decision-diagram engines

`asm/bdd.go` and `prove/solver/bdd.oak` represent a Boolean function as an
edge `2 * node + c`: the node's function when `c = 0`, its negation when
`c = 1`. One terminal node stands for `false`; `true` is its complement.
The laws below are the ones the engines rely on when they normalize a
node (`mk`), decide an `apply` on terminal shapes, and take cofactors of a
complemented edge. Each is a statement about Booleans, decided by cases.
-/

namespace Oak.BddComplement

/-- Shannon's expansion: the function of a node with variable `v`, high
cofactor `h` and low cofactor `l`. -/
def node (v h l : Bool) : Bool := if v then h else l

/-- `mk` normalization: a node whose high edge would be complemented is
stored with both cofactors complemented and the result complemented. -/
theorem mk_complement (v h l : Bool) : node v (!h) (!l) = !(node v h l) := by
  cases v <;> simp [node]

/-- Cofactors of a complemented edge are the complemented cofactors. -/
theorem cofactor_complement (v h l : Bool) : !(node v h l) = node v (!h) (!l) := by
  cases v <;> simp [node]

/-- The terminal cases `apply` adds for an operand equal to the other's
complement, and for `xor` with `true`. -/
theorem and_self_not (x : Bool) : (x && !x) = false := by cases x <;> rfl
theorem or_self_not (x : Bool) : (x || !x) = true := by cases x <;> rfl
theorem xor_self_not (x : Bool) : xor x (!x) = true := by cases x <;> rfl
theorem xor_true (x : Bool) : xor x true = !x := by cases x <;> rfl
theorem true_xor (x : Bool) : xor true x = !x := by cases x <;> rfl

/-- Negation is an involution: the complement bit flips back. -/
theorem not_not (x : Bool) : !(!x) = x := by cases x <;> rfl

/-- A witness path: when a non-constant function's high cofactor is not
`false`, setting the variable makes the function that cofactor, which has
a satisfying assignment by induction; otherwise the low cofactor is the
function under the cleared variable. -/
theorem path_high (h l : Bool) : node true h l = h := rfl
theorem path_low (h l : Bool) : node false h l = l := rfl

end Oak.BddComplement
