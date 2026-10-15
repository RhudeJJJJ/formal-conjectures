/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic

/-! Modal-degree and four-cycle definitions with semantic bridges.
The least mode is proved least among maxima over ALL natural degree values.
OpenAI Codex assisted with formalization. -/
namespace WOWIIModal
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
def frequency (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (univ.filter fun v => G.degree v = d).card

def modalCandidates (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (range (Fintype.card V)).filter fun d =>
    ∀ e ∈ range (Fintype.card V), frequency G e ≤ frequency G d

noncomputable def modeMin (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf (modalCandidates G : Set ℕ)

/-- No cycle on four distinct vertices, including cycles with chords. -/
def C4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma frequency_zero (d : ℕ) (hd : Fintype.card V ≤ d) : frequency G d = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hdeg := G.degree_lt_card_verts v
  have he := (mem_filter.mp hv).2
  omega

omit [DecidableEq V] in
lemma modeMin_spec [Nonempty V] :
    (∀ e : ℕ, frequency G e ≤ frequency G (modeMin G)) ∧
      ∀ d : ℕ, (∀ e : ℕ, frequency G e ≤ frequency G d) → modeMin G ≤ d := by
  classical
  have hn : (range (Fintype.card V)).Nonempty := ⟨0, by simp [Fintype.card_pos]⟩
  obtain ⟨d, hd, hm⟩ := exists_max_image (range (Fintype.card V)) (frequency G) hn
  have hnon : (modalCandidates G : Set ℕ).Nonempty :=
    ⟨d, mem_filter.mpr ⟨hd, hm⟩⟩
  have hmem : modeMin G ∈ modalCandidates G := Nat.sInf_mem hnon
  have hmode := mem_filter.mp hmem
  constructor
  · intro e
    by_cases he : e < Fintype.card V
    · exact hmode.2 e (mem_range.mpr he)
    · rw [frequency_zero G e (by omega)]
      exact Nat.zero_le _
  · intro e he
    by_cases hen : e < Fintype.card V
    · exact Nat.sInf_le (show e ∈ modalCandidates G from
        mem_filter.mpr ⟨mem_range.mpr hen, fun k _ => he k⟩)
    · have hlt := mem_range.mp hmode.1
      omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma no_four_cycle (hG : C4Free G) {a : V} (w : G.Walk a a) (hw : w.IsCycle) :
    w.length ≠ 4 := by
  intro he
  have h02 : w.getVert 0 ≠ w.getVert 2 := by
    intro hh
    have hi := hw.getVert_injOn' (by simp [he]) (by simp [he]) hh
    omega
  have h13 : w.getVert 1 ≠ w.getVert 3 := by
    intro hh
    have hi := hw.getVert_injOn' (by simp [he]) (by simp [he]) hh
    omega
  have h30 : G.Adj (w.getVert 3) (w.getVert 0) := by
    have hs := w.adj_getVert_succ (i := 3) (by omega)
    have h40 : w.getVert 4 = w.getVert 0 := by
      rw [← he, Walk.getVert_length, Walk.getVert_zero]
    simpa only [Nat.reduceAdd, h40] using hs
  exact hG _ _ _ _ h02 h13 (w.adj_getVert_succ (i := 0) (by omega))
    (w.adj_getVert_succ (i := 1) (by omega)) (w.adj_getVert_succ (i := 2) (by omega)) h30

#print axioms modeMin_spec
#print axioms no_four_cycle
end WOWIIModal
