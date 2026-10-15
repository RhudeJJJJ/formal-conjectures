/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-! WOWII 352: the 18-vertex witness from Gebendorfer's 30 August 2026
note, isomorphic to Dubey's earlier public witness. No first-refutation claim.
OpenAI Codex assisted with formalization. Distances use the WOWII 363/360
certificate method. Only one finite witness is needed for universal disproof. -/
namespace WOWII352Proof
open SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def parent : Fin 18 → Fin 18 := ![0,0,1,2,3,4,5,6,7,8,9,10,0,0,0,4,5,6]

def witness : SimpleGraph (Fin 18) where
  Adj v w := v ≠ w ∧ (parent v = w ∨ parent w = v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel fun v w => v ≠ w ∧ (parent v = w ∨ parent w = v))

def delta : Fin 18 → Fin 18 → ℕ := ![
  ![0,1,2,3,4,5,6,7,8,9,10,11,1,1,1,5,6,7],
  ![1,0,1,2,3,4,5,6,7,8,9,10,2,2,2,4,5,6],
  ![2,1,0,1,2,3,4,5,6,7,8,9,3,3,3,3,4,5],
  ![3,2,1,0,1,2,3,4,5,6,7,8,4,4,4,2,3,4],
  ![4,3,2,1,0,1,2,3,4,5,6,7,5,5,5,1,2,3],
  ![5,4,3,2,1,0,1,2,3,4,5,6,6,6,6,2,1,2],
  ![6,5,4,3,2,1,0,1,2,3,4,5,7,7,7,3,2,1],
  ![7,6,5,4,3,2,1,0,1,2,3,4,8,8,8,4,3,2],
  ![8,7,6,5,4,3,2,1,0,1,2,3,9,9,9,5,4,3],
  ![9,8,7,6,5,4,3,2,1,0,1,2,10,10,10,6,5,4],
  ![10,9,8,7,6,5,4,3,2,1,0,1,11,11,11,7,6,5],
  ![11,10,9,8,7,6,5,4,3,2,1,0,12,12,12,8,7,6],
  ![1,2,3,4,5,6,7,8,9,10,11,12,0,2,2,6,7,8],
  ![1,2,3,4,5,6,7,8,9,10,11,12,2,0,2,6,7,8],
  ![1,2,3,4,5,6,7,8,9,10,11,12,2,2,0,6,7,8],
  ![5,4,3,2,1,2,3,4,5,6,7,8,6,6,6,0,3,4],
  ![6,5,4,3,2,1,2,3,4,5,6,7,7,7,7,3,0,3],
  ![7,6,5,4,3,2,1,2,3,4,5,6,8,8,8,4,3,0]]

theorem delta_zero : ∀ u v : Fin 18, delta u v = 0 ↔ u = v := by decide
theorem delta_step : ∀ u v : Fin 18, u ≠ v →
    ∃ w, witness.Adj v w ∧ delta u w + 1 = delta u v := by decide
theorem parent_lipschitz : ∀ u v : Fin 18,
    delta u v ≤ delta u (parent v) + 1 ∧ delta u (parent v) ≤ delta u v + 1 := by decide

theorem delta_lipschitz (u v w : Fin 18) (h : witness.Adj v w) :
    delta u v ≤ delta u w + 1 := by
  rcases h.2 with he | he
  · simpa only [he] using (parent_lipschitz u v).1
  · simpa only [he] using (parent_lipschitz u w).2

theorem walk_certificate (u v : Fin 18) : ∃ p : witness.Walk v u, p.length = delta u v := by
  have aux : ∀ n : ℕ, ∀ v : Fin 18, delta u v = n →
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

theorem delta_le_length (u : Fin 18) {v w : Fin 18} (p : witness.Walk v w) :
    delta u v ≤ p.length + delta u w := by
  induction p with
  | nil => simp
  | @cons v w z ha p ih =>
    have hh := delta_lipschitz u v w ha
    simp only [Walk.length_cons]
    omega

theorem dist_eq_delta (u v : Fin 18) : witness.dist u v = delta u v := by
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
  have he : witness.edgeFinset.card = 17 := by decide
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

def selected : Finset (Fin 18) := {0,1,4,5,6,9,10}
theorem selected_total : witness.IsTotalDominating (selected : Set (Fin 18)) := by
  change ∀ v : Fin 18, ∃ w ∈ selected, witness.Adj v w
  decide
theorem total_bound : witness.totalDominationNumber ≤ 7 :=
  Nat.sInf_le ⟨selected, selected_total, by decide⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
def closedDegreeTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 2 ∨ ∃ u, G.degree u = 2 ∧ G.Adj v u
def maxVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def averageMaxEccentricity (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (∑ v ∈ maxVertices G, Finset.univ.sup (fun w => G.dist v w) : ℕ) /
    ((maxVertices G).card : ℚ)

lemma max_vertices_spec : maxVertices witness = {0} := by decide
lemma average_eq : averageMaxEccentricity witness = 11 := by
  unfold averageMaxEccentricity
  rw [max_vertices_spec]
  simp_rw [dist_eq_delta]
  have hd : Finset.univ.sup (fun w : Fin 18 => delta 0 w) = 11 := by decide
  simp only [Finset.sum_singleton, hd, Finset.card_singleton]
  norm_num

abbrev HVertex := {v : Fin 18 // v ∈ closedDegreeTwo witness}
def H : SimpleGraph HVertex := witness.induce (closedDegreeTwo witness : Set (Fin 18))
instance : DecidableRel H.Adj := inferInstanceAs
  (DecidableRel fun u v : HVertex => witness.Adj u.val v.val)
def leftVertex : HVertex := ⟨0, by decide⟩
def rightVertex : HVertex := ⟨6, by decide⟩
def side (v : HVertex) : Bool := v.val.val < 5
lemma side_preserved : ∀ u v : HVertex, H.Adj u v → side u = side v := by decide
lemma walk_side {u v : HVertex} (p : H.Walk u v) : side u = side v := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih => exact (side_preserved a b hab).trans ih

lemma component_lower : 2 ≤ Nat.card H.ConnectedComponent := by
  classical
  have hne : H.connectedComponentMk leftVertex ≠ H.connectedComponentMk rightVertex := by
    intro he
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact he
    have h := walk_side p
    have hl : side leftVertex = true := by decide
    have hr : side rightVertex = false := by decide
    rw [hl,hr] at h
    contradiction
  let f : Fin 2 → H.ConnectedComponent := fun i =>
    if i = 0 then H.connectedComponentMk leftVertex else H.connectedComponentMk rightVertex
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · change H.connectedComponentMk leftVertex = H.connectedComponentMk rightVertex at hij
      exact (hne hij).elim
    · change H.connectedComponentMk rightVertex = H.connectedComponentMk leftVertex at hij
      exact (hne hij.symm).elim
    · rfl
  have hc := Nat.card_le_card_of_injective (f := f) hf
  simpa using hc

theorem conjecture352 : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card W →
      Nat.card (G.induce (closedDegreeTwo G : Set W)).ConnectedComponent +
        ⌈averageMaxEccentricity G / 2⌉₊ ≤ G.totalDominationNumber := by
  intro h
  have hh := h (Fin 18) witness witness_tree (by decide)
  rw [average_eq] at hh
  have he : ⌈(11 : ℚ) / 2⌉₊ = 6 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num
  rw [he] at hh
  have hc : 2 ≤ Nat.card (witness.induce
      (closedDegreeTwo witness : Set (Fin 18))).ConnectedComponent := component_lower
  have ht := total_bound
  omega

#print axioms dist_eq_delta
#print axioms witness_tree
#print axioms component_lower
#print axioms average_eq
#print axioms conjecture352
end WOWII352Proof
