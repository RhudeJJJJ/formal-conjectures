/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Closed proposition checks of the two exact fixed-case statements.
No third-party statement aliases occur in the expected types below.
-/
import Proofs.Erdos617R5Proof
import Proofs.Erdos617R6Proof
import Proofs.Erdos617BoundaryAudit

example : ∀ {V : Type} [Fintype V] [DecidableEq V],
    Fintype.card V = 5 ^ 2 + 1 → ∀ coloring : Sym2 V → Fin 5,
      ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  Gebendorfer.Erdos617R5.r_eq_5

example : ∀ {V : Type} [Fintype V] [DecidableEq V],
    Fintype.card V = 6 ^ 2 + 1 → ∀ coloring : Sym2 V → Fin 6,
      ∃ (S : Finset V) (k : Fin 6), S.card = 6 + 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  Gebendorfer.Erdos617R6.r_eq_6

#print axioms Gebendorfer.Erdos617R5.r_eq_5
#print axioms Gebendorfer.Erdos617R6.r_eq_6
#print axioms Gebendorfer.Erdos617Boundary.r_two_shape_false
