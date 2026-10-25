import FormalConjectures.Other.GraphicalBell
import Proofs.GraphicalBell.Base

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

noncomputable def total (G : SimpleGraph V) (S : Finset V) : ℕ := Nat.card (Parts G S)

noncomputable def gradedEquiv (G : SimpleGraph V) (S : Finset V) :
    Parts G S ≃ Σ k : Fin (S.card + 1), Graded G S k.val where
  toFun P := ⟨⟨P.val.card, Nat.lt_succ_of_le (stable_card_le P.property)⟩, P, rfl⟩
  invFun Q := Q.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨P, hp⟩⟩
    cases hp
    rfl

open scoped Classical in
lemma total_eq_sum [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    total G S = ∑ k : Fin (S.card + 1), count G S k.val := by
  rw [total, Nat.card_congr (gradedEquiv G S), Nat.card_sigma]
  rfl

lemma original_stirling_eq_count [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    PHOEG.GraphicalBell.stirling G k = count G univ k := by
  apply Nat.card_congr
  exact
    { toFun := fun P => ⟨⟨P.val, P.property.1⟩, P.property.2⟩
      invFun := fun P => ⟨P.val.val, P.val.property, P.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma original_bell_eq_total [Fintype V] (G : SimpleGraph V) :
    PHOEG.GraphicalBell.bell G = total G univ := rfl

open scoped Classical in
lemma original_bell_eq_sum [Fintype V] (G : SimpleGraph V) :
    PHOEG.GraphicalBell.bell G =
      ∑ k : Fin (Fintype.card V + 1), PHOEG.GraphicalBell.stirling G k.val := by
  rw [original_bell_eq_total, total_eq_sum]
  rw [card_univ]
  apply Finset.sum_congr
  · ext k; simp
  · intro k _
    exact (original_stirling_eq_count G k.val).symm

universe u
open scoped Classical in
lemma bell_of_coefficientwise
    (hcoeff : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj], 1 ≤ Fintype.card W → ∀ k : ℕ,
      PHOEG.GraphicalBell.stirling
        (PHOEG.GraphicalBell.quasiComplete (Fintype.card W) G.edgeFinset.card) k ≤
      PHOEG.GraphicalBell.stirling G k)
    {W : Type u} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (hn : 1 ≤ Fintype.card W) :
    PHOEG.GraphicalBell.bell
      (PHOEG.GraphicalBell.quasiComplete (Fintype.card W) G.edgeFinset.card) ≤
      PHOEG.GraphicalBell.bell G := by
  rw [original_bell_eq_sum, original_bell_eq_sum]
  exact Finset.sum_le_sum (fun (k : Fin (Fintype.card W + 1)) _ => hcoeff G hn k.val)

end GraphicalBellProof
