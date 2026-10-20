import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! The elementary sparse-graph part of Erdős--Gyárfás, Lemma 1 (1999).
OpenAI Codex assisted with formalization. -/

namespace Erdos617ThreeCore
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

def DiamondFree (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ d → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → False

def NoIndependentFour (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 4 → ¬ G.IsIndepSet (S : Set V)

lemma triangle_of_no_independent_three (G : SimpleGraph V) (X : Finset V)
    (hX : 6 ≤ X.card)
    (h3 : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c →
      G.Adj a b ∨ G.Adj a c ∨ G.Adj b c) :
    ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  by_contra! ht
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < X.card)
  let N := X.filter (G.Adj v)
  let A := X.filter fun w => w ≠ v ∧ ¬ G.Adj v w
  have hN : N.card ≤ 2 := by
    by_contra! h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp h
    obtain ⟨haX, hva⟩ := mem_filter.mp ha
    obtain ⟨hbX, hvb⟩ := mem_filter.mp hb
    obtain ⟨hcX, hvc⟩ := mem_filter.mp hc
    have hnab : ¬ G.Adj a b := ht v hv a haX b hbX hva hvb
    have hnac : ¬ G.Adj a c := ht v hv a haX c hcX hva hvc
    have hnbc : ¬ G.Adj b c := ht v hv b hbX c hcX hvb hvc
    exact (h3 a haX b hbX c hcX hab hac hbc).elim hnab (fun h => h.elim hnac hnbc)
  have hAA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b := by
    intro a ha b hb hab
    obtain ⟨haX, hav, hvna⟩ := mem_filter.mp ha
    obtain ⟨hbX, hbv, hvnb⟩ := mem_filter.mp hb
    exact (h3 v hv a haX b hbX hav.symm hbv.symm hab).resolve_left hvna |>.resolve_left hvnb
  have hA : A.card ≤ 2 := by
    by_contra! h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp h
    exact ht a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 c (mem_filter.mp hc).1
      (hAA a ha b hb hab) (hAA a ha c hc hac) (hAA b hb c hc hbc)
  have hs : X ⊆ insert v (N ∪ A) := by
    intro w hw
    by_cases he : w = v
    · simp [he]
    by_cases hadj : G.Adj v w
    · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hw,hadj⟩))
    · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨hw,he,hadj⟩))
  have hc := (card_le_card hs).trans (card_insert_le v (N ∪ A))
  have hu := card_union_le N A
  omega

lemma no_low_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 10) (h4 : NoIndependentFour G) (hd : DiamondFree G) :
    ∀ v, 3 ≤ G.degree v := by
  classical
  intro v
  by_contra! hv
  let X := univ \ insert v (G.neighborFinset v)
  have hX : 7 ≤ X.card := by
    have hn : v ∉ G.neighborFinset v := by simp
    have he := card_insert_of_notMem hn
    have hc := card_sdiff_of_subset (subset_univ (insert v (G.neighborFinset v)))
    have hdg := G.card_neighborFinset_eq_degree v
    dsimp [X]
    rw [hc,card_univ,hV,he,hdg]
    omega
  have hx : ∀ a ∈ X, a ≠ v ∧ ¬ G.Adj v a := by
    intro a ha
    simpa [X, mem_neighborFinset, adj_comm] using ha
  have h3 : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c →
      G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
    intro a ha b hb c hc hab hac hbc
    by_contra! hn
    have hs : ({v,a,b,c} : Finset V).card = 4 := by
      simp [hab,hac,hbc,(hx a ha).1,(hx b hb).1,(hx c hc).1,
        Ne.symm (hx a ha).1,Ne.symm (hx b hb).1,Ne.symm (hx c hc).1]
    apply h4 {v,a,b,c} hs
    intro x hxs y hys hxy
    simp only [Finset.mem_coe, mem_insert, mem_singleton] at hxs hys
    rcases hxs with rfl | rfl | rfl | rfl <;>
      rcases hys with rfl | rfl | rfl | rfl <;>
      simp_all [adj_comm]
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ :=
    triangle_of_no_independent_three G X (by omega) h3
  let Z := X \ {a,b,c}
  have hZ : 4 ≤ Z.card := by
    have he : ({a,b,c} : Finset V).card = 3 := by
      simp [hab.ne,hac.ne,hbc.ne]
    have hsub : ({a,b,c} : Finset V) ⊆ X := by simp [insert_subset_iff,ha,hb,hc]
    dsimp [Z]
    rw [card_sdiff_of_subset hsub,he]
    omega
  have hz : ∀ z ∈ Z, z ∈ X ∧ a ≠ z ∧ b ≠ z ∧ c ≠ z := by
    intro z hz
    simpa [Z,ne_comm, and_assoc] using hz
  have hcomplete : ∀ u ∈ Z, ∀ w ∈ Z, u ≠ w → G.Adj u w := by
    intro u hu w hw huw
    by_contra hn
    have cover : ∀ y ∈ ({a,b,c} : Finset V), G.Adj y u ∨ G.Adj y w := by
      intro y hy
      have hyX : y ∈ X := by
        simp only [mem_insert,mem_singleton] at hy
        rcases hy with rfl|rfl|rfl
        · exact ha
        · exact hb
        · exact hc
      have hyu : y ≠ u := by
        simp only [mem_insert,mem_singleton] at hy
        rcases hy with rfl|rfl|rfl
        · exact (hz u hu).2.1
        · exact (hz u hu).2.2.1
        · exact (hz u hu).2.2.2
      have hyw : y ≠ w := by
        simp only [mem_insert,mem_singleton] at hy
        rcases hy with rfl|rfl|rfl
        · exact (hz w hw).2.1
        · exact (hz w hw).2.2.1
        · exact (hz w hw).2.2.2
      rcases h3 y hyX u (hz u hu).1 w (hz w hw).1 hyu hyw huw with h|h|h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hn h).elim
    have ca := cover a (by simp)
    have cb := cover b (by simp)
    have cc := cover c (by simp)
    rcases ca with ca|ca <;> rcases cb with cb|cb <;> rcases cc with cc|cc
    · exact hd a b c u (hz u hu).2.1 (hz u hu).2.2.1 (hz u hu).2.2.2 hab hac hbc ca cb
    · exact hd a b c u (hz u hu).2.1 (hz u hu).2.2.1 (hz u hu).2.2.2 hab hac hbc ca cb
    · exact hd a c b u (hz u hu).2.1 (hz u hu).2.2.2 (hz u hu).2.2.1 hac hab hbc.symm ca cc
    · exact hd b c a w (hz w hw).2.2.1 (hz w hw).2.2.2 (hz w hw).2.1 hbc hab.symm hac.symm cb cc
    · exact hd b c a u (hz u hu).2.2.1 (hz u hu).2.2.2 (hz u hu).2.1 hbc hab.symm hac.symm cb cc
    · exact hd a c b w (hz w hw).2.1 (hz w hw).2.2.2 (hz w hw).2.2.1 hac hab hbc.symm ca cc
    · exact hd a b c w (hz w hw).2.1 (hz w hw).2.2.1 (hz w hw).2.2.2 hab hac hbc ca cb
    · exact hd a b c w (hz w hw).2.1 (hz w hw).2.2.1 (hz w hw).2.2.2 hab hac hbc ca cb
  obtain ⟨d,hdZ,e,heZ,f,hfZ,g,hgZ,hde,hdf,hdg,hef,heg,hfg⟩ := three_lt_card.mp (by omega : 3 < Z.card)
  exact hd d e f g hdg heg hfg (hcomplete d hdZ e heZ hde)
    (hcomplete d hdZ f hfZ hdf) (hcomplete e heZ f hfZ hef)
    (hcomplete d hdZ g hgZ hdg) (hcomplete e heZ g hgZ heg)

end Erdos617ThreeCore
