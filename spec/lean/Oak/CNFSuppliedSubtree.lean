import Oak.CNFSuppliedRefutation

/-!
# Structural restriction to a named original-clause subtree

The relation records only a path through the existing ordered tree. A model
of the whole tree restricts to each subtree, so a clause consequence proved
inside a named subtree lifts to the original database. Generated applications
must supply kernel-checked constructor witnesses for the actual tree path.
-/

set_option autoImplicit false

namespace Oak.CNFSuppliedRefutation

open Oak.RupCheck Oak.TseitinCNF

inductive Original.Subtree : Original → Original → Prop where
  | refl (tree : Original) : Subtree tree tree
  | left {left right part : Original} (included : Subtree left part) :
      Subtree (.branch left right) part
  | right {left right part : Original} (included : Subtree right part) :
      Subtree (.branch left right) part

theorem Original.Subtree.models {whole part : Original}
    (included : Original.Subtree whole part) (assignment : Assignment) :
    SatisfiesClauses assignment whole.toList → SatisfiesClauses assignment part.toList := by
  induction included with
  | refl tree =>
      intro model
      exact model
  | left included ih =>
      intro model
      apply ih
      intro clause member
      exact model clause (List.mem_append_left _ member)
  | right included ih =>
      intro model
      apply ih
      intro clause member
      exact model clause (List.mem_append_right _ member)

theorem Original.Subtree.lift_consequence {whole part : Original} {clause : Clause}
    (included : Original.Subtree whole part)
    (consequence : Consequence part.toList clause) : Consequence whole.toList clause := by
  intro assignment model
  exact consequence assignment (included.models assignment model)

end Oak.CNFSuppliedRefutation
