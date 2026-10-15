/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-! WOWII 363: a complete finite counterexample from Gebendorfer's 14 October 2026
manuscript. OpenAI Codex assisted with formalization. The distance-certificate
argument adapts the previously published WOWII 360 construction. -/
namespace WOWII363Proof
open SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def parent : Fin 27 → Fin 27 := ![0,0,1,2,3,4,0,6,7,8,9,2,7,0,13,14,13,15,15,15,15,15,15,15,15,15,15]

def witness : SimpleGraph (Fin 27) where
  Adj v w := v ≠ w ∧ (parent v = w ∨ parent w = v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel fun v w => v ≠ w ∧ (parent v = w ∨ parent w = v))

def delta : Fin 27 → Fin 27 → ℕ := ![
  ![0,1,2,3,4,5,1,2,3,4,5,3,3,1,2,3,2,4,4,4,4,4,4,4,4,4,4],
  ![1,0,1,2,3,4,2,3,4,5,6,2,4,2,3,4,3,5,5,5,5,5,5,5,5,5,5],
  ![2,1,0,1,2,3,3,4,5,6,7,1,5,3,4,5,4,6,6,6,6,6,6,6,6,6,6],
  ![3,2,1,0,1,2,4,5,6,7,8,2,6,4,5,6,5,7,7,7,7,7,7,7,7,7,7],
  ![4,3,2,1,0,1,5,6,7,8,9,3,7,5,6,7,6,8,8,8,8,8,8,8,8,8,8],
  ![5,4,3,2,1,0,6,7,8,9,10,4,8,6,7,8,7,9,9,9,9,9,9,9,9,9,9],
  ![1,2,3,4,5,6,0,1,2,3,4,4,2,2,3,4,3,5,5,5,5,5,5,5,5,5,5],
  ![2,3,4,5,6,7,1,0,1,2,3,5,1,3,4,5,4,6,6,6,6,6,6,6,6,6,6],
  ![3,4,5,6,7,8,2,1,0,1,2,6,2,4,5,6,5,7,7,7,7,7,7,7,7,7,7],
  ![4,5,6,7,8,9,3,2,1,0,1,7,3,5,6,7,6,8,8,8,8,8,8,8,8,8,8],
  ![5,6,7,8,9,10,4,3,2,1,0,8,4,6,7,8,7,9,9,9,9,9,9,9,9,9,9],
  ![3,2,1,2,3,4,4,5,6,7,8,0,6,4,5,6,5,7,7,7,7,7,7,7,7,7,7],
  ![3,4,5,6,7,8,2,1,2,3,4,6,0,4,5,6,5,7,7,7,7,7,7,7,7,7,7],
  ![1,2,3,4,5,6,2,3,4,5,6,4,4,0,1,2,1,3,3,3,3,3,3,3,3,3,3],
  ![2,3,4,5,6,7,3,4,5,6,7,5,5,1,0,1,2,2,2,2,2,2,2,2,2,2,2],
  ![3,4,5,6,7,8,4,5,6,7,8,6,6,2,1,0,3,1,1,1,1,1,1,1,1,1,1],
  ![2,3,4,5,6,7,3,4,5,6,7,5,5,1,2,3,0,4,4,4,4,4,4,4,4,4,4],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,0,2,2,2,2,2,2,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,0,2,2,2,2,2,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,0,2,2,2,2,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,0,2,2,2,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,2,0,2,2,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,2,2,0,2,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,2,2,2,0,2,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,2,2,2,2,0,2,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,2,2,2,2,2,0,2],
  ![4,5,6,7,8,9,5,6,7,8,9,7,7,3,2,1,4,2,2,2,2,2,2,2,2,2,0]]

theorem delta_zero : ∀ u v : Fin 27, delta u v = 0 ↔ u = v := by decide
theorem delta_step : ∀ u v : Fin 27, u ≠ v →
    ∃ w, witness.Adj v w ∧ delta u w + 1 = delta u v := by decide
theorem parent_lipschitz : ∀ u v : Fin 27,
    delta u v ≤ delta u (parent v) + 1 ∧ delta u (parent v) ≤ delta u v + 1 := by decide

theorem delta_lipschitz (u v w : Fin 27) (h : witness.Adj v w) :
    delta u v ≤ delta u w + 1 := by
  rcases h.2 with he | he
  · simpa only [he] using (parent_lipschitz u v).1
  · simpa only [he] using (parent_lipschitz u w).2

theorem walk_certificate (u v : Fin 27) : ∃ p : witness.Walk v u, p.length = delta u v := by
  have aux : ∀ n : ℕ, ∀ v : Fin 27, delta u v = n →
      ∃ p : witness.Walk v u, p.length = delta u v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases he : u = v
      · subst v
        exact ⟨.nil, (delta_zero u u).mpr rfl |>.symm⟩
      · obtain ⟨w, ha, hd⟩ := delta_step u v he
        obtain ⟨p, hp⟩ := ih (delta u w) (by omega) w rfl
        exact ⟨.cons ha p, by simp only [Walk.length_cons, hp]; omega⟩
  exact aux _ v rfl

theorem witness_connected : witness.Connected :=
  ⟨fun u v => (walk_certificate v u).elim fun p _ => p.reachable⟩

theorem delta_le_length (u : Fin 27) {v w : Fin 27} (p : witness.Walk v w) :
    delta u v ≤ p.length + delta u w := by
  induction p with
  | nil => simp
  | @cons v w z ha p ih =>
    have hh := delta_lipschitz u v w ha
    simp only [Walk.length_cons]
    omega

theorem dist_eq_delta (u v : Fin 27) : witness.dist u v = delta u v := by
  apply Nat.le_antisymm
  · obtain ⟨p, hp⟩ := walk_certificate u v
    have h := SimpleGraph.dist_le p.reverse
    simpa only [Walk.length_reverse, hp] using h
  · obtain ⟨p, hp⟩ := witness_connected.exists_walk_length_eq_dist v u
    have h := delta_le_length u p
    rw [hp, witness.dist_comm] at h
    simpa only [(delta_zero u u).mpr rfl, Nat.add_zero] using h

theorem witness_tree : witness.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨witness_connected, ?_⟩
  have he : witness.edgeFinset.card = 26 := by decide
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

def selected : Finset (Fin 27) := {2,3,4,7,8,9,13,14,15}
theorem selected_total : witness.IsTotalDominating (selected : Set (Fin 27)) := by
  change ∀ v : Fin 27, ∃ w ∈ selected, witness.Adj v w
  decide
theorem total_bound : witness.totalDominationNumber ≤ 9 :=
  Nat.sInf_le ⟨selected, selected_total, by decide⟩

noncomputable def boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w,
    Finset.univ.sup (fun x => G.dist w x) ≤ Finset.univ.sup (fun x => G.dist v x)

noncomputable def distanceTo {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) (v : V) : ℕ := by
  classical
  exact if h : B.Nonempty then B.inf' h (fun b => G.dist v b) else 0

noncomputable def positiveBoundaryAverage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℚ :=
  (∑ v ∈ Finset.univ \ boundary G, distanceTo G (boundary G) v : ℕ) /
    (((Finset.univ \ boundary G).card : ℕ) : ℚ)

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def isolatedSupports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  (supports G).filter fun v => ∀ w ∈ supports G, ¬ G.Adj v w

theorem boundary_spec : boundary witness = {5,10} := by
  classical
  unfold boundary
  simp_rw [dist_eq_delta]
  decide

theorem isolated_supports_card : (isolatedSupports witness).card = 6 := by decide

theorem average_eq : positiveBoundaryAverage witness = 151 / 25 := by
  unfold positiveBoundaryAverage
  rw [boundary_spec]
  simp_rw [distanceTo]
  have hb : ({5,10} : Finset (Fin 27)).Nonempty := by decide
  simp only [dif_pos hb]
  simp_rw [dist_eq_delta]
  have hn : (∑ v ∈ (Finset.univ \ {5,10} : Finset (Fin 27)),
      ({5,10} : Finset (Fin 27)).inf' (by decide) (fun b => delta v b)) = 151 := by decide
  rw [hn]
  have hc : (Finset.univ \ {5,10} : Finset (Fin 27)).card = 25 := by decide
  rw [hc]
  norm_num

theorem counterexample : witness.IsTree ∧ 2 < Fintype.card (Fin 27) ∧
    (witness.totalDominationNumber : ℚ) <
      (isolatedSupports witness).card + positiveBoundaryAverage witness / 2 := by
  refine ⟨witness_tree, by decide, ?_⟩
  rw [isolated_supports_card, average_eq]
  have ht : (witness.totalDominationNumber : ℚ) ≤ 9 := by exact_mod_cast total_bound
  norm_num only [Nat.cast_ofNat]
  linarith

theorem conjecture363 : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      ((isolatedSupports G).card : ℚ) + positiveBoundaryAverage G / 2 ≤
        G.totalDominationNumber := by
  intro h
  exact (not_le_of_gt counterexample.2.2)
    (h (Fin 27) witness witness_tree (by decide))

#print axioms dist_eq_delta
#print axioms witness_tree
#print axioms average_eq
#print axioms conjecture363
end WOWII363Proof
