/-
Copyright 2026 Jonas J. Gebendorfer.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module
public import Proofs.WOWII9684.Charge
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace WOWII96
open SimpleGraph Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Maximum local independence one forces the whole connected graph to be complete. -/
theorem complete_of_local_le_one (hc : G.Connected)
    (hM : ∀ v, indepNeighborsCard G v ≤ 1) :
    ∀ x y, x ≠ y → G.Adj x y := by
  classical
  intro x y hxy
  by_contra hn
  have hd := hc.one_lt_dist_of_ne_of_not_adj hxy hn
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨a, b, c, hab, hbc, hac, hne⟩ := p.exists_adj_adj_not_adj_ne hp hd
  have hi : G.IsIndepSet (({a,c} : Finset V) : Set V) := by
    intro u hu v hv huv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · exact hac
    · exact fun h => hac h.symm
    · exact (huv rfl).elim
  have hnbr : ∀ z ∈ ({a,c} : Finset V), G.Adj b z := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hab.symm
    · exact hbc
  have hb := (local_card_bound b {a,c} hi hnbr).trans (hM b)
  simp [hne] at hb

/-- The real-valued original bound holds at each choice of root. -/
theorem bound_for_root [Nontrivial V] (hc : G.Connected) (r : V) (M : ℕ)
    (hM : ∀ v, indepNeighborsCard G v ≤ M) :
    (G.indepNum : ℝ) ≤ 1 + (distEven G r : ℝ) * ((M : ℝ) - 1) := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hMpos : 1 ≤ M := (local_positive hc r).trans (hM r)
  by_cases hM2 : 2 ≤ M
  · have hb := independent_bound hc r I hI.1 M hM hM2
    rw [hI.2] at hb
    have hbR : (G.indepNum : ℝ) ≤ 1 + (distEven G r : ℝ) * ((M - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb
    rwa [Nat.cast_sub hMpos, Nat.cast_one] at hbR
  · have hM1 : M = 1 := by omega
    have hcomplete := complete_of_local_le_one hc (by simpa [hM1] using hM)
    have hcard : I.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      by_contra hxy
      exact hI.1 hx hy hxy (hcomplete x y hxy))
    rw [hI.2] at hcard
    have hcardR : (G.indepNum : ℝ) ≤ 1 := by exact_mod_cast hcard
    simpa [hM1] using hcardR

/-- The complete exact nontrivial-graph statement in Formal Conjectures. -/
theorem full_conjecture96 [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    (hc : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  classical
  dsimp only
  let M := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
  have hM : ∀ v, indepNeighborsCard G v ≤ M := by
    intro v
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image (distEven G)) (by simp))
  have hb := bound_for_root hc r M hM
  simpa only [hr] using hb

end WOWII96
