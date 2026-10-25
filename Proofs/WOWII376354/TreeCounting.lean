import Proofs.WOWII376354.MedianGeometry
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Rooted incidence injections and total-domination cover counts on tree halves. -/

open Finset SimpleGraph
namespace WOWIIMedian
variable {V : Type*} [Fintype V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

noncomputable def child (r u v : V) : V := if T.dist r u<T.dist r v then v else u

omit [Fintype V] [DecidableRel T.Adj] in
lemma child_ne_root (hT : T.IsTree) {r u v : V} (huv : T.Adj u v) :
    child T r u v≠r := by
  have hstep := hT.dist_eq_dist_add_one_of_adj r huv
  unfold child
  split_ifs with h
  · intro he;subst v;simp only [T.dist_self] at *;omega
  · intro he;subst u;simp only [T.dist_self] at *;omega

omit [Fintype V] [DecidableRel T.Adj] in
lemma child_injective (hT : T.IsTree) (r : V) (I : Finset V)
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬T.Adj u v) :
    Function.Injective (fun p : (Σ u : I, T.neighborSet u.val) => child T r p.1.val p.2.val) := by
  classical
  rintro ⟨⟨u,hu⟩,⟨v,huv⟩⟩ ⟨⟨x,hx⟩,⟨y,hxy⟩⟩ he
  change child T r u v=child T r x y at he
  change T.Adj u v at huv
  change T.Adj x y at hxy
  have hs := hT.dist_eq_dist_add_one_of_adj r huv
  have ht := hT.dist_eq_dist_add_one_of_adj r hxy
  by_cases hlt : T.dist r u<T.dist r v <;>
    by_cases hlt' : T.dist r x<T.dist r y
  · simp only [child,hlt,hlt',↓reduceIte] at he
    subst y
    have hux : u=x := WOWIIGeometry.closer_unique T hT (w:=r) huv.symm hxy.symm
      (by omega) (by omega)
    subst x
    rfl
  · simp only [child,hlt,hlt',↓reduceIte] at he
    subst x
    exact False.elim (hI u hu v hx huv)
  · simp only [child,hlt,hlt',↓reduceIte] at he
    subst u
    exact False.elim (hI x hx y hu hxy)
  · simp only [child,hlt,hlt',↓reduceIte] at he
    subst x
    have hvy : v=y := WOWIIGeometry.closer_unique T hT (w:=r) huv hxy (by omega) (by omega)
    subst y
    rfl

lemma independent_incidence_bound (hT : T.IsTree) (r : V) (I W : Finset V)
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬T.Adj u v)
    (hW : ∀ u ∈ I, ∀ v, T.Adj u v → child T r u v ∈ W) :
    ∑ u ∈ I, T.degree u ≤ W.card := by
  classical
  let f : (Σ u : I, T.neighborSet u.val) → W :=
    fun p => ⟨child T r p.1.val p.2.val,hW _ p.1.property _ p.2.property⟩
  have hinj : Function.Injective f := by
    intro p q he
    exact child_injective T hT r I hI (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective f hinj
  have hcard : Fintype.card (Σ u : I, T.neighborSet u.val)=∑ u ∈ I, T.degree u := by
    rw [Fintype.card_sigma]
    simp only [T.card_neighborSet_eq_degree]
    exact Finset.sum_coe_sort I (fun u => T.degree u)
  rw [hcard,Fintype.card_coe] at hc
  exact hc

lemma independent_global_bound (hT : T.IsTree) (I : Finset V)
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬T.Adj u v) :
    ∑ u ∈ I, T.degree u < Fintype.card V := by
  classical
  let r := Classical.choice hT.connected.nonempty
  have hh := independent_incidence_bound T hT r I (univ.erase r) hI (by
    intro u hu v huv
    exact mem_erase.mpr ⟨child_ne_root T hT huv,mem_univ _⟩)
  have hc := Finset.card_erase_add_one (mem_univ r)
  simp only [card_univ] at hc
  omega

lemma independent_side_bound [DecidableEq V] (hT : T.IsTree) {a b : V} (hab : T.Adj a b)
    (I : Finset V) (hIS : I ⊆ side T a b)
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬T.Adj u v) :
    ∑ u ∈ I, T.degree u ≤ (side T a b).card-1+(if a ∈ I then 1 else 0) := by
  classical
  let S := side T a b
  let B : Finset V := if a ∈ I then {b} else ∅
  have hbound := independent_incidence_bound T hT a I (S.erase a ∪ B) hI (by
    intro u hu v huv
    by_cases hv : v ∈ S
    · apply mem_union_left
      apply mem_erase.mpr
      refine ⟨child_ne_root T hT huv,?_⟩
      unfold child
      split_ifs
      · exact hv
      · exact hIS hu
    · have hv' : v ∈ side T b a := by
        rw [side_compl T hT hab]
        simpa only [mem_compl] using hv
      obtain ⟨rfl,rfl⟩ := side_cross_edge T hT hab (hIS hu) hv' huv
      apply mem_union_right
      simp only [B,hu,↓reduceIte,child,T.dist_self,T.dist_eq_one_iff_adj.mpr hab,
        Nat.zero_lt_one,mem_singleton]
  )
  have hc := Finset.card_union_le (S.erase a) B
  have ha : a ∈ S := side_root T hab
  have hcard : (S.erase a).card=S.card-1 := card_erase_of_mem ha
  have hB : B.card=if a ∈ I then 1 else 0 := by
    unfold B
    split_ifs <;> simp
  dsimp only [S] at *
  omega

lemma cover_sum_bound (X D : Finset V)
    (hcover : ∀ v ∈ X, ∃ d ∈ D, T.Adj v d) : X.card ≤ ∑ d ∈ D, T.degree d := by
  classical
  have hsub : X ⊆ D.biUnion (fun d => T.neighborFinset d) := by
    intro v hv
    obtain ⟨d,hd,hvd⟩ := hcover v hv
    exact mem_biUnion.mpr ⟨d,hd,by simpa using hvd.symm⟩
  have h := (card_le_card hsub).trans (card_biUnion_le)
  simpa only [T.card_neighborFinset_eq_degree] using h

variable [DecidableEq V]

def internalDegree (S : Finset V) (v : V) : ℕ := (T.neighborFinset v ∩ S).card

lemma internal_le_degree (S : Finset V) (v : V) : internalDegree T S v ≤ T.degree v := by
  change (T.neighborFinset v ∩ S).card ≤ T.degree v
  exact (card_le_card inter_subset_left).trans_eq (T.card_neighborFinset_eq_degree v)

lemma internal_lt_at_boundary {S : Finset V} {a b : V}
    (hab : T.Adj a b) (hb : b ∉ S) : internalDegree T S a < T.degree a := by
  have hss : T.neighborFinset a ∩ S ⊂ T.neighborFinset a := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨inter_subset_left,?_⟩
    intro he
    have hbm : b ∈ T.neighborFinset a := by simpa using hab
    rw [← he] at hbm
    exact hb (mem_inter.mp hbm).2
  simpa only [internalDegree,T.card_neighborFinset_eq_degree] using card_lt_card hss

lemma side_cover_bound (hT : T.IsTree) {a b : V} (hab : T.Adj a b)
    {D : Finset V} (hD : T.IsTotalDominating (D : Set V)) :
    (side T a b).card-1 ≤ ∑ d ∈ D ∩ side T a b, internalDegree T (side T a b) d := by
  classical
  let S := side T a b
  have hsub : S.erase a ⊆ (D ∩ S).biUnion (fun d => T.neighborFinset d ∩ S) := by
    intro v hv
    obtain ⟨d,hd,hvd⟩ := hD v
    have hvS := (mem_erase.mp hv).2
    have hdS : d ∈ S := by
      by_contra hdS
      have hd' : d ∈ side T b a := by rw [side_compl T hT hab];simpa using hdS
      have he := side_cross_edge T hT hab hvS hd' hvd
      exact (mem_erase.mp hv).1 he.1
    exact mem_biUnion.mpr ⟨d,mem_inter.mpr ⟨hd,hdS⟩,
      mem_inter.mpr ⟨by simpa using hvd.symm,hvS⟩⟩
  have h := (card_le_card hsub).trans (card_biUnion_le)
  have ha : a ∈ S := side_root T hab
  simpa only [card_erase_of_mem ha,internalDegree,S] using h

end WOWIIMedian
