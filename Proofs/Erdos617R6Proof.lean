/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.

Exact-statement bridge to Nick Winter's full formalization of Robert Sneiderman's
r=6 proof. Pinned source: nwinter/erdos-617-r5 @
32f1bfe6759299ef3a1c6e8b4c3c637528a9881b. Source port to Lean 4.33.1 is
recorded separately. This is not a claim of authorship of the earlier proof or
its formalization, nor a line-by-line formalization of Gebendorfer's later paper.
-/
import Lean617.R6.Brooks

namespace Gebendorfer.Erdos617R6

/-- The exact r=6 conclusion for every 37-element finite vertex type. -/
theorem r_eq_6 {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 6 ^ 2 + 1) (coloring : Sym2 V → Fin 6) :
    ∃ (S : Finset V) (k : Fin 6), S.card = 6 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  Erdos617.R6.main6_imp_upstream Erdos617.R6.erdos_617_r6_unconditional hV coloring

#print axioms Erdos617.R6.erdos_617_r6_unconditional
#print axioms r_eq_6

end Gebendorfer.Erdos617R6
