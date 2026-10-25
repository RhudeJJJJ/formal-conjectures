import Proofs.GraphicalBell.Insertion

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

noncomputable def degreeOn (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ := by
  classical
  exact (S.filter (G.Adj v)).card

lemma choices_bound {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)}
    (hP : StableOn G S P) (v : V) :
    P.card - degreeOn G S v ≤ Nat.card (Choices G P v) := by
  classical
  let free : Finset (Finset V) := P.filter (fun B => ∀ w ∈ B, ¬ G.Adj v w)
  let bad : Finset (Finset V) := P.filter (fun B => ∃ w ∈ B, G.Adj v w)
  let N : Finset V := S.filter (G.Adj v)
  have hcard : Nat.card (Choices G P v) = free.card := by
    have e : Choices G P v ≃ free :=
      { toFun := fun B => ⟨B.val, mem_filter.mpr B.property⟩
        invFun := fun B => ⟨B.val, mem_filter.mp B.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    simp
  let f : bad → N := fun B =>
    let w := Classical.choose (mem_filter.mp B.property).2
    have hw := Classical.choose_spec (mem_filter.mp B.property).2
    ⟨w, mem_filter.mpr ⟨stable_subset hP (mem_filter.mp B.property).1 hw.1, hw.2⟩⟩
  have hf : Function.Injective f := by
    intro B C he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    have hb := Classical.choose_spec (mem_filter.mp B.property).2
    have hc := Classical.choose_spec (mem_filter.mp C.property).2
    exact stable_unique hP (mem_filter.mp B.property).1 (mem_filter.mp C.property).1
      hb.1 (by simpa only [f] using he' ▸ hc.1)
  have hbcard : bad.card ≤ N.card := Finset.card_le_card_of_injective hf
  have hsum : free.card + bad.card = P.card := by
    have h := card_filter_add_card_filter_not P (fun B => ∀ w ∈ B, ¬ G.Adj v w)
    simpa only [free, bad, not_forall, not_not] using h
  rw [hcard]
  change P.card - N.card ≤ free.card
  omega

open scoped Classical in
lemma deletion_lower {G : SimpleGraph V} {S : Finset V} {v : V}
    (hv : v ∉ S) (k : ℕ) :
    count G S k + (k + 1 - degreeOn G S v) * count G S (k + 1) ≤
      count G (insert v S) (k + 1) := by
  rw [count_insert hv k]
  apply Nat.add_le_add_left
  calc
    (k + 1 - degreeOn G S v) * count G S (k + 1) =
        ∑ _P : Graded G S (k + 1), (k + 1 - degreeOn G S v) := by
          simp [count, Nat.card_eq_fintype_card, mul_comm]
    _ ≤ ∑ P : Graded G S (k + 1), Nat.card (Choices G P.val.val v) := by
      apply sum_le_sum
      intro P _
      have h := choices_bound P.val.property v
      simpa only [P.property] using h

end GraphicalBellProof
