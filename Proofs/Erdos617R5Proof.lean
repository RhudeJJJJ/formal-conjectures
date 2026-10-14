/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.

Complete fixed r=5 theorem obtained by a new composition of existing formal work.
Graph-theoretic reduction: Ramazan Kara's erdos-617-r5-formal-verification,
pin 578c1f3f4ad336a07ab5ea6841042e474bfb3443 (following Robert Sneiderman).
Generic Brooks proof: Nick Winter, nwinter/erdos-617-r5,
pin 32f1bfe6759299ef3a1c6e8b4c3c637528a9881b, following Mariusz Zając.
This bridge replaces the special Brooks SAT branch by the general theorem.
It certifies the same fixed-case statement as Gebendorfer's paper; it is not a
line-by-line formalization or a priority claim for that paper's proof route.
-/
import Erdos617.ResidualDegreeFive
import Proofs.ZajacBrooks
import Proofs.Erdos617R5Transport

namespace Gebendorfer.Erdos617R5

/-- The previously held special Brooks proposition, with no hypotheses remaining. -/
theorem specialBrooks : Erdos617.R5SpecialBrooksObstruction := by
  intro G _ hregular _ hclique hindep
  have hcolor := Gebendorfer.Zajac.brooks_zajac 5 (by norm_num) G
    (fun v => le_of_eq (hregular v)) hclique
  exact Erdos617.indepSetFree_six_not_colorable_five_fin26 G hindep hcolor

/-- The full r=5 statement in the foreign project's exact edge model. -/
theorem fixed_case : Erdos617.Problem617At 5 :=
  Erdos617.problem617At_five_of_special_brooks specialBrooks

/-- The exact arbitrary-vertex-type statement used by formal-conjectures. -/
theorem r_eq_5 {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 5 ^ 2 + 1) (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  apply transport fixed_case (by simpa using hV) coloring

#print axioms specialBrooks
#print axioms fixed_case
#print axioms r_eq_5

end Gebendorfer.Erdos617R5
