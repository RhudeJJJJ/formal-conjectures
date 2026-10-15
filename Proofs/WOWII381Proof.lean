/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! WOWII 381. A direct covering proof of Gebendorfer's support-degree bound.
OpenAI Codex assisted with formalization. -/
namespace WOWII381Proof
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def neighbors (S : Finset V) : Finset V :=
  univ.filter fun v => ∃ s ∈ S, G.Adj v s

def isolates (S : Finset V) : Finset V :=
  S.filter fun v => ∀ w ∈ S, ¬ G.Adj v w

def supports : Finset V := univ.filter fun s => ∃ p, G.degree p = 1 ∧ G.Adj s p

def supportDegree : ℕ := (supports G).sup (fun v => G.degree v)

omit [DecidableEq V] in
lemma mem_neighbors (S : Finset V) (v : V) :
    v ∈ neighbors G S ↔ ∃ s ∈ S, G.Adj v s := by simp [neighbors]
lemma mem_isolates (S : Finset V) (v : V) :
    v ∈ isolates G S ↔ v ∈ S ∧ ∀ w ∈ S, ¬ G.Adj v w := by simp [isolates]

/-- The covering argument works for any prescribed subset of a total dominating set. -/
theorem covering_bound (S D : Finset V) (b : ℕ) (hb : 2 ≤ b)
    (hSD : S ⊆ D) (hD : G.IsTotalDominating (D : Set V))
    (hdeg : ∀ s ∈ S, G.degree s ≤ b) :
    (isolates G (neighbors G S)).card ≤ (b - 1) * D.card := by
  let J := isolates G S
  have hJS : J ⊆ S := filter_subset _ _
  have hZ : isolates G (neighbors G S) ⊆ neighbors G J := by
    intro v hv
    obtain ⟨hvN, hvI⟩ := (mem_isolates G _ v).mp hv
    obtain ⟨s, hs, hvs⟩ := (mem_neighbors G S v).mp hvN
    apply (mem_neighbors G J v).mpr
    refine ⟨s, (mem_isolates G S s).mpr ⟨hs, ?_⟩, hvs⟩
    intro t ht hst
    exact hvI s ((mem_neighbors G S s).mpr ⟨t, ht, hst⟩) hvs
  have hres : ∀ j ∈ J, ((G.neighborFinset j) \ D).card ≤ b - 1 := by
    intro j hj
    obtain ⟨w, hwD, hjw⟩ := hD j
    have hw : w ∈ G.neighborFinset j := by simpa using hjw
    calc
      ((G.neighborFinset j) \ D).card ≤ ((G.neighborFinset j).erase w).card := by
        apply card_le_card
        intro v hv
        obtain ⟨hvn, hvD⟩ := mem_sdiff.mp hv
        apply mem_erase.mpr
        exact ⟨fun he => hvD (he ▸ hwD), hvn⟩
      _ = G.degree j - 1 := by rw [card_erase_of_mem hw, G.card_neighborFinset_eq_degree]
      _ ≤ b - 1 := Nat.sub_le_sub_right (hdeg j (hJS hj)) 1
  have hcover : neighbors G J ⊆ (D \ S) ∪ J.biUnion (fun j => G.neighborFinset j \ D) := by
    intro v hv
    obtain ⟨j, hj, hvj⟩ := (mem_neighbors G J v).mp hv
    by_cases hvD : v ∈ D
    · apply mem_union_left
      apply mem_sdiff.mpr
      refine ⟨hvD, ?_⟩
      intro hvS
      exact ((mem_isolates G S j).mp hj).2 v hvS hvj.symm
    · apply mem_union_right
      apply mem_biUnion.mpr
      exact ⟨j, hj, mem_sdiff.mpr ⟨by simpa using hvj.symm, hvD⟩⟩
  have hJcard : J.card ≤ S.card := card_le_card hJS
  have hsplit : (D \ S).card + S.card = D.card := card_sdiff_add_card_eq_card hSD
  calc
    (isolates G (neighbors G S)).card ≤ (neighbors G J).card := card_le_card hZ
    _ ≤ ((D \ S) ∪ J.biUnion (fun j => G.neighborFinset j \ D)).card := card_le_card hcover
    _ ≤ (D \ S).card + (J.biUnion (fun j => G.neighborFinset j \ D)).card := card_union_le _ _
    _ ≤ (D \ S).card + J.card * (b - 1) := Nat.add_le_add_left (card_biUnion_le_card_mul _ _ _ hres) _
    _ ≤ (D \ S).card * (b - 1) + S.card * (b - 1) := by
      apply Nat.add_le_add
      · exact Nat.le_mul_of_pos_right _ (by omega)
      · exact Nat.mul_le_mul_right _ hJcard
    _ = (b - 1) * D.card := by rw [← Nat.add_mul, hsplit, Nat.mul_comm]

omit [DecidableEq V] in
lemma supports_subset_total (D : Finset V) (hD : G.IsTotalDominating (D : Set V)) :
    supports G ⊆ D := by
  intro s hs
  obtain ⟨p, hp, hsp⟩ := (mem_filter.mp hs).2
  obtain ⟨w, hwD, hpw⟩ := hD p
  obtain ⟨q, _, hq⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hp
  have hws : w = s := (hq w hpw).trans (hq s hsp.symm).symm
  exact hws ▸ hwD

/-- Connected graphs of order at least three cannot have adjacent leaves. -/
theorem no_adjacent_leaves (hG : G.Connected) (hn : 2 < Fintype.card V) :
    ∀ p q, G.degree p = 1 → G.degree q = 1 → ¬ G.Adj p q := by
  intro p q hp hq hpq
  have up : ∀ z, G.Adj p z → z = q := by
    obtain ⟨s, _, hs⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hp
    intro z hz
    exact (hs z hz).trans (hs q hpq).symm
  have uq : ∀ z, G.Adj q z → z = p := by
    obtain ⟨s, _, hs⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hq
    intro z hz
    exact (hs z hz).trans (hs p hpq.symm).symm
  have walk_closed : ∀ {a b}, G.Walk a b → (a = p ∨ a = q) → (b = p ∨ b = q) := by
    intro a b w
    induction w with
    | nil => exact id
    | @cons a b c hab w ih =>
      intro ha
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (up b hab)
      · exact Or.inl (uq b hab)
  have hsub : (univ : Finset V) ⊆ {p,q} := by
    intro v _
    obtain ⟨w⟩ := hG p v
    simpa only [mem_insert, mem_singleton] using walk_closed w (Or.inl rfl)
  have hc := (card_le_card hsub).trans (Finset.card_le_two (a := p) (b := q))
  rw [Finset.card_univ] at hc
  omega

lemma support_degree_ge_two (hG : G.Connected) (hn : 2 < Fintype.card V)
    {s : V} (hs : s ∈ supports G) : 2 ≤ G.degree s := by
  obtain ⟨p, hp, hsp⟩ := (mem_filter.mp hs).2
  have hpos : 0 < G.degree s := (G.degree_pos_iff_exists_adj s).mpr ⟨p,hsp⟩
  have hne : G.degree s ≠ 1 := fun he => no_adjacent_leaves G hG hn s p he hp hsp
  omega

lemma supportDegree_ge_two (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    2 ≤ supportDegree G := by
  have : Nontrivial V := (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨p,hp⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨s, hps⟩ := hT.connected.preconnected.exists_adj_of_nontrivial p
  have hs : s ∈ supports G := mem_filter.mpr ⟨mem_univ _, ⟨p,hp,hps.symm⟩⟩
  exact (support_degree_ge_two G hT.connected hn hs).trans
    (Finset.le_sup (f := fun v => G.degree v) hs)

/-- The conjectured bound for all finite trees of order greater than two. -/
theorem conjecture381 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    (isolates G (neighbors G (supports G))).card ≤
      (supportDegree G - 1) * G.totalDominationNumber := by
  have : Nontrivial V := (Fintype.one_lt_card_iff_nontrivial).mp (by omega)
  have hdeg : ∀ v ∈ supports G, G.degree v ≤ supportDegree G := by
    intro v hv
    exact Finset.le_sup (f := fun v => G.degree v) hv
  have hb := supportDegree_ge_two G hT hn
  have hall : G.IsTotalDominating ((univ : Finset V) : Set V) := by
    intro v
    obtain ⟨w,hw⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
    exact ⟨w, mem_univ _, hw⟩
  have hnon : {n | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card V, univ, hall, card_univ⟩
  obtain ⟨D,hD⟩ := Nat.sInf_mem hnon
  have hc : D.card = G.totalDominationNumber := hD.card_eq
  rw [← hc]
  exact covering_bound G (supports G) D (supportDegree G) hb
    (supports_subset_total G D hD.isTotalDominating) hD.isTotalDominating hdeg

/-- The original quotient form, with degree measured in the ambient tree. -/
theorem conjecture381_ratio (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    ((isolates G (neighbors G (supports G))).card : ℚ) /
      ((supportDegree G : ℚ) - 1) ≤ G.totalDominationNumber := by
  have hb := supportDegree_ge_two G hT hn
  have hbq : (2 : ℚ) ≤ supportDegree G := by exact_mod_cast hb
  have hcast : ((isolates G (neighbors G (supports G))).card : ℚ) ≤
      ((supportDegree G - 1 : ℕ) : ℚ) * (G.totalDominationNumber : ℚ) := by
    exact_mod_cast conjecture381 G hT hn
  rw [Nat.cast_sub (by omega : 1 ≤ supportDegree G), Nat.cast_one] at hcast
  apply (div_le_iff₀ (by linarith : (0 : ℚ) < (supportDegree G : ℚ) - 1)).mpr
  nlinarith

#print axioms covering_bound
#print axioms conjecture381
#print axioms conjecture381_ratio
end WOWII381Proof
