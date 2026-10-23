import FormalConjectures.WrittenOnTheWallII.GraphConjecture361
import Proofs.WOWII361362.GraphCover
import Proofs.WOWII361362.TreeCenter

/-! Complete certificates for the exact submitted tree bounds.
The proof imports the original problem definitions and uses only proved helpers. -/

namespace WrittenOnTheWallII.GraphConjecture361
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma supports_forced (T : SimpleGraph V) [DecidableRel T.Adj]
    {D : Finset V} (hD : T.IsTotalDominating (D : Set V)) : supports T ⊆ D := by
  intro s hs
  obtain ⟨l,hl,hsl⟩ := (mem_filter.mp hs).2
  exact WOWIICover.forced_support T hD hl hsl

lemma support_center_set_bound (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 1 < Fintype.card V)
    (D : Finset V) (hD : T.IsTotalDominating (D : Set V)) :
    (isolatedSupports T).card + Nat.card T.center ≤ D.card := by
  classical
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp horder
  let _ := hT.connected.nonempty
  have hSD := supports_forced T hD
  have hc := WOWIIGeometry.center_card_le_two T hT
  have hDtwo : 2 ≤ D.card := by
    obtain ⟨w,hw,_⟩ := hD (Classical.ofNonempty : V)
    obtain ⟨x,hx,hwx⟩ := hD w
    exact one_lt_card.mpr ⟨w,hw,x,hx,hwx.ne⟩
  by_cases hbig : 2 < Fintype.card V
  swap
  · have hvcard : Fintype.card V=2 := by omega
    have hI : isolatedSupports T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨w,hvw⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
      have hdpos := (T.degree_pos_iff_exists_adj v).mpr ⟨w,hvw⟩
      have hdlt := T.degree_lt_card_verts v
      have hd : T.degree v=1 := by omega
      have hwS : w ∈ supports T := by
        apply mem_filter.mpr
        exact ⟨mem_univ _,v,hd,hvw.symm⟩
      exact (mem_filter.mp hv).2 w hwS hvw
    rw [hI,card_empty]
    omega
  by_cases he : ∃ a ∈ supports T, ∃ b ∈ supports T, T.Adj a b
  · obtain ⟨a,ha,b,hb,hab⟩ := he
    have haI : a ∉ isolatedSupports T := fun h =>
      (mem_filter.mp h).2 b hb hab
    have hbI : b ∉ isolatedSupports T := fun h =>
      (mem_filter.mp h).2 a ha hab.symm
    have hsub : insert a (insert b (isolatedSupports T)) ⊆ D := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hSD ha
      rcases mem_insert.mp hx with rfl | hx
      · exact hSD hb
      exact hSD (mem_filter.mp hx).1
    have hcard : (insert a (insert b (isolatedSupports T))).card =
        (isolatedSupports T).card+2 := by
      simp [haI,hbI,hab.ne,Nat.add_assoc]
    have hbnd := card_le_card hsub
    rw [hcard] at hbnd
    omega
  have hIndependent : ∀ a ∈ supports T, ∀ b ∈ supports T, ¬ T.Adj a b := by
    intro a ha b hb hab
    exact he ⟨a,ha,b,hb,hab⟩
  have hIeq : isolatedSupports T=supports T := by
    ext v
    constructor
    · intro hv; exact (mem_filter.mp hv).1
    · intro hv
      exact mem_filter.mpr ⟨hv,hIndependent v hv⟩
  rw [hIeq]
  by_cases hlarge : (supports T).card+2 ≤ D.card
  · omega
  obtain ⟨l,hl⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨s,hls⟩ := hT.connected.preconnected.exists_adj_of_nontrivial l
  have hs : s ∈ supports T := mem_filter.mpr ⟨mem_univ _,l,hl,hls.symm⟩
  obtain ⟨w,hw,hsw⟩ := hD s
  have hwS : w ∉ supports T := fun h => hIndependent s hs w h hsw
  have hsplus : (supports T).card+1 ≤ D.card := by
    have hsub : insert w (supports T) ⊆ D := insert_subset hw hSD
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hwS] at hcard
    exact hcard
  have hdiff : (D \ supports T).card=1 := by
    rw [card_sdiff_of_subset hSD]
    omega
  obtain ⟨z,hzEq⟩ := card_eq_one.mp hdiff
  have hzmem : z ∈ D \ supports T := by rw [hzEq]; simp
  have hzD := (mem_sdiff.mp hzmem).1
  have hzS := (mem_sdiff.mp hzmem).2
  have honly : ∀ d ∈ D, d ∈ supports T ∨ d=z := by
    intro d hd
    by_cases hds : d ∈ supports T
    · exact Or.inl hds
    right
    have hm : d ∈ D \ supports T := mem_sdiff.mpr ⟨hd,hds⟩
    rw [hzEq,mem_singleton] at hm
    exact hm
  have hadjS : ∀ s ∈ supports T, T.Adj z s := by
    intro a ha
    obtain ⟨d,hd,had⟩ := hD a
    rcases honly d hd with hs | rfl
    · exact (hIndependent a ha d hs had).elim
    · exact had.symm
  have hzNoLeaves : ∀ t, T.Adj z t → T.degree t ≠ 1 := by
    intro t hzt hdeg
    exact hzS (mem_filter.mpr ⟨mem_univ _,t,hdeg,hzt⟩)
  have hdepth : ∀ v, T.dist z v ≤ 2 := by
    intro v
    obtain ⟨d,hd,hvd⟩ := hD v
    rcases honly d hd with hs | rfl
    · have hzd := hadjS d hs
      have ht := hT.connected.dist_triangle (u:=z) (v:=d) (w:=v)
      rw [T.dist_eq_one_iff_adj.mpr hzd,T.dist_eq_one_iff_adj.mpr hvd.symm] at ht
      exact ht
    · rw [T.dist_eq_one_iff_adj.mpr hvd.symm]
      omega
  have hc1 := WOWIIGeometry.center_card_of_depth_two T hT hbig z hzNoLeaves hdepth
  omega

theorem full_conjecture361_nontrivial (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 1 < Fintype.card V) :
    (isolatedSupports T).card + Nat.card T.center ≤ T.totalDominationNumber := by
  classical
  obtain ⟨D,hD,hcard⟩ := WOWIICover.minimum_total_set T hT.connected horder
  simpa only [hcard] using support_center_set_bound T hT horder D hD

theorem full_conjecture361 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) :
    (isolatedSupports T).card + Nat.card T.center ≤ T.totalDominationNumber :=
  full_conjecture361_nontrivial T hT (by omega)

#print axioms full_conjecture361_nontrivial
#print axioms full_conjecture361
end WrittenOnTheWallII.GraphConjecture361
