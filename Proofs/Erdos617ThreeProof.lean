import FormalConjectures.ErdosProblems.«617»
import Proofs.Erdos617ThreeCore
import Proofs.ZajacBrooks
import Mathlib.Tactic

/-!
Complete certificate for the classical three-colour case of Erdős 617.
The argument follows Erdős and Gyárfás (1999), Lemma 1, pp. 84--85.
The inherited Brooks theorem is Nick Winter's formalization of Zając's proof.
OpenAI Codex assisted with the new formalization and exact-target bridge.
-/

namespace Erdos617ThreeProof
open Finset SimpleGraph Erdos617ThreeCore
variable {V : Type} [Fintype V] [DecidableEq V]

def colorGraph (c : Sym2 V → Fin 3) (k : Fin 3) : SimpleGraph V where
  Adj u v := u ≠ v ∧ c s(u,v) = k
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

instance (c : Sym2 V → Fin 3) (k : Fin 3) : DecidableRel (colorGraph c k).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = _))

lemma minority (hV : Fintype.card V = 10) (c : Sym2 V → Fin 3) :
    ∃ k, (colorGraph c k).edgeFinset.card ≤ 15 := by
  classical
  have he (k : Fin 3) : (colorGraph c k).edgeFinset =
      (⊤ : SimpleGraph V).edgeFinset.filter (fun e => c e = k) := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        mem_filter, SimpleGraph.top_adj]; rfl
  have hsum : (∑ k : Fin 3, (colorGraph c k).edgeFinset.card) = 45 := by
    simp_rw [he]
    rw [← card_eq_sum_card_fiberwise (f := c) (s := (⊤ : SimpleGraph V).edgeFinset)
      (t := univ) (fun _ _ => mem_univ _)]
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two,hV]
    decide
  by_contra! hn
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  simp only [Fin.sum_univ_succ] at hsum
  change (colorGraph c 0).edgeFinset.card +
    ((colorGraph c 1).edgeFinset.card + ((colorGraph c 2).edgeFinset.card + 0)) = 45 at hsum
  omega

lemma third_colour (a b : Fin 3) : ∃ k : Fin 3, k ≠ a ∧ k ≠ b := by
  revert a b
  decide

lemma diamond_forbidden (c : Sym2 V → Fin 3) (k : Fin 3)
    (hbal : ∀ S : Finset V, S.card = 4 →
      ∀ ell : Fin 3, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u,v) = ell) :
    DiamondFree (colorGraph c k) := by
  intro a b d e hae hbe hde hab had hbd hae' hbe'
  obtain ⟨ell,hellk,helle⟩ := third_colour k (c s(d,e))
  have hcard : ({a,b,d,e} : Finset V).card = 4 := by
    simp [hab.1,had.1,hbd.1,hae,hbe,hde]
  obtain ⟨u,hu,v,hv,huv,he⟩ := hbal {a,b,d,e} hcard ell
  have hkell := hellk.symm
  have heell := helle.symm
  change a ≠ b ∧ c s(a,b) = k at hab
  change a ≠ d ∧ c s(a,d) = k at had
  change b ≠ d ∧ c s(b,d) = k at hbd
  change a ≠ e ∧ c s(a,e) = k at hae'
  change b ≠ e ∧ c s(b,e) = k at hbe'
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl|rfl <;>
    simp_all [Sym2.eq_swap]

omit [Fintype V] [DecidableEq V] in
lemma no_four_clique (G : SimpleGraph V) (hd : DiamondFree G) : G.CliqueFree 4 := by
  intro S hS
  obtain ⟨a,ha,b,hb,c,hc,d,hdS,hab,hac,had,hbc,hbd,hcd⟩ :=
    three_lt_card.mp (show 3 < S.card by rw [hS.card_eq]; decide)
  exact hd a b c d had hbd hcd (hS.isClique ha hb hab) (hS.isClique ha hc hac)
    (hS.isClique hb hc hbc) (hS.isClique ha hdS had) (hS.isClique hb hdS hbd)

lemma degree_le_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 10) (hm : G.edgeFinset.card ≤ 15)
    (hd : ∀ v, 3 ≤ G.degree v) : ∀ v, G.degree v ≤ 3 := by
  intro v
  have hrest : 27 ≤ ∑ w ∈ univ.erase v, G.degree w := by
    calc
      27 = ∑ _w ∈ univ.erase v, 3 := by simp [hV]
      _ ≤ _ := sum_le_sum (fun w _ => hd w)
  have he : (∑ w ∈ univ.erase v, G.degree w) + G.degree v =
      ∑ w : V, G.degree w := sum_erase_add _ _ (mem_univ v)
  have hs := G.sum_degrees_eq_twice_card_edges
  omega

omit [DecidableEq V] in
lemma independent_four_of_colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 10) (hC : G.Colorable 3) :
    ∃ S : Finset V, S.card = 4 ∧ G.IsIndepSet (S : Set V) := by
  classical
  obtain ⟨f⟩ := hC
  have he : (∑ k : Fin 3, (univ.filter fun v => f v = k).card) = 10 := by
    rw [← card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ)
      (fun _ _ => mem_univ _),card_univ,hV]
  have hex : ∃ k : Fin 3, 4 ≤ (univ.filter fun v => f v = k).card := by
    by_contra! hn
    have hb : (∑ k : Fin 3, (univ.filter fun v => f v = k).card) ≤ 9 := by
      calc
        _ ≤ ∑ _k : Fin 3, 3 := sum_le_sum (fun k _ => by have := hn k; omega)
        _ = 9 := by decide
    omega
  obtain ⟨k,hk⟩ := hex
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq hk
  refine ⟨S,hcard,?_⟩
  intro a ha b hb _ hab
  have hfa := (mem_filter.mp (hS ha)).2
  have hfb := (mem_filter.mp (hS hb)).2
  exact f.valid hab (hfa.trans hfb.symm)

theorem three (hV : Fintype.card V = 10) (c : Sym2 V → Fin 3) :
    ∃ S : Finset V, ∃ k : Fin 3, S.card = 4 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  classical
  by_contra! hbal
  have hb : ∀ S : Finset V, S.card = 4 →
      ∀ k : Fin 3, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u,v) = k := by
    intro S hS k
    simpa only [not_forall,_root_.not_imp,not_not] using hbal S k hS
  obtain ⟨k,hm⟩ := minority hV c
  let G := colorGraph c k
  have h4 : NoIndependentFour G := by
    intro S hS hI
    obtain ⟨u,hu,v,hv,huv,he⟩ := hb S hS k
    exact hI hu hv huv ⟨huv,he⟩
  have hd : DiamondFree G := diamond_forbidden c k hb
  have hdeg := degree_le_three G hV hm (no_low_degree G hV h4 hd)
  have hC := Gebendorfer.Zajac.brooks_zajac 3 (by decide) G hdeg (no_four_clique G hd)
  obtain ⟨S,hS,hI⟩ := independent_four_of_colorable G hV hC
  exact h4 S hS hI

theorem r_eq_3 (_r : ℕ) (_hr : _r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 3^2 + 1) (c : Sym2 V → Fin 3) :
    ∃ (S : Finset V) (k : Fin 3), S.card = 3 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  exact three hV c

end Erdos617ThreeProof

#print axioms Erdos617ThreeProof.r_eq_3
