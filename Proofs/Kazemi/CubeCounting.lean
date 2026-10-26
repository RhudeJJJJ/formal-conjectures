module

public import Proofs.Kazemi.Geometry
public import Mathlib.Algebra.Ring.Parity

/-! # Common-neighborhood capacities and matching bounds in Boolean cubes

The capacity bound counts an active class and its common open neighborhood.
The independent-set matching argument also records the equality implication.
The closed-neighborhood parity lemma is the geometric input to van Wee's bound.
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Independent (C : Finset (Vertex ι)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ¬ (cube ι).Adj x y

def Dominates (D : Finset (Vertex ι)) : Prop :=
  ∀ v, (D ∩ closedBall v).Nonempty

def TotallyDominates (D : Finset (Vertex ι)) : Prop :=
  ∀ v, ∃ w ∈ D, (cube ι).Adj v w

theorem common_singleton (x : Vertex ι) : common {x} = neighbors x := by
  ext y
  simp [mem_common, (cube ι).adj_comm]

theorem common_capacity {C : Finset (Vertex ι)} (hd : 3 ≤ Fintype.card ι)
    (hC : C.Nonempty) (hA : (common C).Nonempty) :
    C.card + (common C).card ≤ Fintype.card ι + 1 := by
  by_cases h1 : C.card = 1
  · obtain ⟨x, rfl⟩ := card_eq_one.1 h1
    simp [common_singleton, Nat.add_comm]
  by_cases h2 : C.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 h2
    have := common_pair_card_le_two hxy
    simp only [card_pair hxy] at *
    omega
  · have h3 : 3 ≤ C.card := by have := hC.card_pos; omega
    obtain ⟨v, hv⟩ := hA
    have hs : C ⊆ neighbors v := fun w hw => mem_neighbors.2 (mem_common.1 hv w hw)
    have hc := card_le_card hs
    rw [card_neighbors] at hc
    have := common_card_le_one h3
    omega

theorem independent_le_compl (i : ι) {R : Finset (Vertex ι)} (hR : Independent R) :
    R.card ≤ Rᶜ.card := by
  have hs : R.image (fun x => flip x i) ⊆ Rᶜ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
    simp only [mem_compl]
    intro hf
    exact hR x hx (flip x i) hf (adj_flip x i)
  calc
    R.card = (R.image (fun x => flip x i)).card := by
      rw [card_image_of_injective _ (flip_coordinate_injective i)]
    _ ≤ Rᶜ.card := card_le_card hs

theorem independent_compl_of_card_eq {R : Finset (Vertex ι)} (hR : Independent R)
    (hcard : R.card = Rᶜ.card) : Independent Rᶜ := by
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := (adj_iff_flip x y).1 hxy
  have hs : R.image (fun x => flip x i) ⊆ Rᶜ := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hz
    exact mem_compl.2 fun hf => hR v hv (flip v i) hf (adj_flip v i)
  have heq : R.image (fun x => flip x i) = Rᶜ :=
    eq_of_subset_of_card_le hs (by rw [card_image_of_injective _ (flip_coordinate_injective i)]; exact hcard.ge)
  have hy' : y ∈ R.image (fun x => flip x i) := by rw [heq]; exact hy
  obtain ⟨v, hv, hvy⟩ := mem_image.1 hy'
  have hvx : v = x := (flip_coordinate_injective i) (hvy.trans hi.symm)
  exact (mem_compl.1 hx) (hvx ▸ hv)

theorem common_pair_even {x y : Vertex ι} (hxy : x ≠ y) :
    Even (common {x,y}).card := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  have hab : flip x i ≠ flip y i := fun h => hxy ((flip_coordinate_injective i) h)
  have he : (cube ι).Adj x (flip y i) ↔ (cube ι).Adj y (flip x i) := by
    simpa only [flip_twice, (cube ι).adj_comm] using (adj_flip_both y (flip x i) i)
  by_cases hp : (cube ι).Adj y (flip x i)
  · have heq : common {x,y} = {flip x i, flip y i} := by
      apply Subset.antisymm (common_pair_subset hi)
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · apply mem_common.2
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with hw | hw
        · rw [hw]; exact (adj_flip x i).symm
        · rw [hw]; exact hp.symm
      · apply mem_common.2
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with hw | hw
        · rw [hw]; exact (he.2 hp).symm
        · rw [hw]; exact (adj_flip y i).symm
    rw [heq, card_pair hab]
    decide
  · have heq : common {x,y} = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro z hz
      have hc := mem_common.1 hz
      have hz' := common_pair_subset hi hz
      simp only [mem_insert, mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact hp ((hc y (by simp)).symm)
      · exact hp (he.1 ((hc x (by simp)).symm))
    rw [heq, card_empty]
    exact ⟨0, rfl⟩

theorem closedBall_inter_even {x y : Vertex ι} (hxy : x ≠ y) :
    Even (closedBall x ∩ closedBall y).card := by
  by_cases ha : (cube ι).Adj x y
  · obtain ⟨i, hi⟩ := (adj_iff_flip x y).1 ha
    have hback : flip y i = x := by rw [← hi, flip_twice]
    have hdiff : x i ≠ y i := by rw [← hi]; simp
    have heq : closedBall x ∩ closedBall y = {x,y} := by
      ext z
      constructor
      · intro hz
        obtain ⟨hzx, hzy⟩ := mem_inter.1 hz
        rcases mem_closedBall.1 hzx with rfl | hzx
        · simp
        rcases mem_closedBall.1 hzy with rfl | hzy
        · simp
        have hc : z ∈ common {x,y} := by
          apply mem_common.2
          intro w hw
          simp only [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hzx.symm
          · exact hzy.symm
        have := common_pair_subset hdiff hc
        simpa only [hi, hback, mem_insert, mem_singleton, or_comm] using this
      · intro hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_inter.2 ⟨mem_closedBall.2 (Or.inl rfl), mem_closedBall.2 (Or.inr ha.symm)⟩
        · exact mem_inter.2 ⟨mem_closedBall.2 (Or.inr ha), mem_closedBall.2 (Or.inl rfl)⟩
    rw [heq, card_pair hxy]
    decide
  · have heq : closedBall x ∩ closedBall y = common {x,y} := by
      ext z
      constructor
      · intro hz
        obtain ⟨hx, hy⟩ := mem_inter.1 hz
        have hx' : (cube ι).Adj x z := by
          rcases mem_closedBall.1 hx with rfl | hx
          · rcases mem_closedBall.1 hy with h | h
            · exact False.elim (hxy h)
            · exact False.elim (ha h.symm)
          · exact hx
        have hy' : (cube ι).Adj y z := by
          rcases mem_closedBall.1 hy with rfl | hy
          · exact False.elim (ha hx')
          · exact hy
        apply mem_common.2
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx'.symm
        · exact hy'.symm
      · intro hz
        have hc := mem_common.1 hz
        exact mem_inter.2 ⟨mem_closedBall.2 (Or.inr (hc x (by simp)).symm),
          mem_closedBall.2 (Or.inr (hc y (by simp)).symm)⟩
    rw [heq]
    exact common_pair_even hxy

end Kazemi.Certificate
