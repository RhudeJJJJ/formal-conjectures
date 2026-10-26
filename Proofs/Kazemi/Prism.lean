module

public import Proofs.Kazemi.EvenBound
public import Proofs.Kazemi.Parity

/-! # The bipartite-prism lower bound in coordinate form

The two parity parts of a total dominating set in an Option-indexed cube project
to dominating sets of the base cube. Van Wee's bound applies to each projection.
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem parity_projection_dominates {S : Finset (Vertex (Option ι))}
    (hS : TotallyDominates S) (p : ZMod 2) :
    Dominates ((S.filter (fun w => parity w = p)).image restrict) := by
  intro v
  obtain ⟨x, hx, hxp⟩ := exists_parity_lift v (p + 1)
  obtain ⟨w, hw, hxw⟩ := hS x
  have hwp : parity w = p := by
    rw [parity_of_adj hxw, hxp, add_assoc, zmod_two_add_self, add_zero]
  have hclose : restrict w ∈ closedBall v := by
    obtain ⟨j, hj⟩ := (adj_iff_flip x w).1 hxw
    rw [← hj]
    cases j with
    | none => rw [restrict_flip_none, hx]; exact mem_closedBall.2 (Or.inl rfl)
    | some i => rw [restrict_flip_some, hx]; exact mem_closedBall.2 (Or.inr (adj_flip v i))
  exact ⟨restrict w, mem_inter.2 ⟨mem_image.2 ⟨w, mem_filter.2 ⟨hw, hwp⟩, rfl⟩, hclose⟩⟩

theorem option_cube_total_domination {S : Finset (Vertex (Option ι))}
    (hS : TotallyDominates S) (hm : 2 ≤ Fintype.card ι)
    (heven : Even (Fintype.card ι)) :
    Fintype.card (Vertex (Option ι)) ≤ Fintype.card ι * S.card := by
  have hp : ∀ p : ZMod 2, Fintype.card (Vertex ι) ≤
      Fintype.card ι * (S.filter (fun w => parity w = p)).card := by
    intro p
    have h := even_dimension_domination (parity_projection_dominates hS p) hm heven
    exact h.trans (Nat.mul_le_mul_left _ (card_image_le))
  have hzero := hp 0
  have hone := hp 1
  have hsplit := parity_parts_card S
  have hc : Fintype.card (Vertex (Option ι)) = 2 * Fintype.card (Vertex ι) := by
    simp [Vertex, pow_succ, Nat.mul_comm]
  rw [hc]
  calc
    2 * Fintype.card (Vertex ι) ≤
        Fintype.card ι * (S.filter (fun w => parity w = 0)).card +
          Fintype.card ι * (S.filter (fun w => parity w = 1)).card := by omega
    _ = _ := by rw [← Nat.mul_add, hsplit]

end Kazemi.Certificate
