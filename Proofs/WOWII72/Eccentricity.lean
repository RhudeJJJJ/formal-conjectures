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
public import Proofs.WOWII72.Graph
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace WOWII72
open SimpleGraph Finset

set_option maxRecDepth 1000000 in
theorem adjacent_to_attachment : ∀ x : Fin 31, x ≠ 24 → x ≠ 26 → x ≠ 27 → H.Adj x 24 := by decide

/-- The actual dense graph is connected, via its path and clique attachment. -/
theorem connected : H.Connected := by
  have h25 : H.Reachable 25 24 := (show H.Adj 25 24 by decide).reachable
  have h26 : H.Reachable 26 24 := (show H.Adj 26 25 by decide).reachable.trans h25
  have h27 : H.Reachable 27 24 := (show H.Adj 27 26 by decide).reachable.trans h26
  have hr : ∀ x : Fin 31, H.Reachable x 24 := by
    intro x
    by_cases h24 : x = 24
    · subst x; exact .rfl
    by_cases hx26 : x = 26
    · simpa [hx26] using h26
    by_cases hx27 : x = 27
    · simpa [hx27] using h27
    exact (adjacent_to_attachment x h24 hx26 hx27).reachable
  exact ⟨fun x y => (hr x).trans (hr y).symm⟩

/-- A one-Lipschitz integer potential gives a lower bound on every walk length. -/
theorem potential_le_walk {V : Type*} {G : SimpleGraph V} (f : V → ℕ)
    (hf : ∀ a b, G.Adj a b → f a ≤ f b + 1) {u v : V} (p : G.Walk u v) :
    f u ≤ f v + p.length := by
  induction p with
  | nil => simp
  | @cons u w v huw p ih =>
    have he := hf u w huw
    rw [Walk.length_cons]
    omega

/-- The same lower bound holds for the graph's actual metric. -/
theorem potential_le_dist {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    (f : V → ℕ) (hf : ∀ a b, G.Adj a b → f a ≤ f b + 1) (t : V) (ht : f t = 0) (x : V) :
    f x ≤ G.dist x t := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x t
  simpa only [ht, zero_add, hp] using potential_le_walk f hf p

def leftPotential (x : Fin 31) : ℕ :=
  if x.val < 24 then 4 else if x.val = 24 then 3 else if x.val = 25 then 2
  else if x.val = 26 then 1 else if x.val = 27 then 0 else 2

def rightPotential (x : Fin 31) : ℕ :=
  if x.val < 24 then (if x.val = 0 then 0 else 1) else if x.val = 24 then 1
  else if x.val = 25 then 2 else if x.val = 26 then 3 else if x.val = 27 then 4 else 2

def eccLower (x : Fin 31) : ℕ := max (leftPotential x) (rightPotential x)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem left_lipschitz : ∀ a b, H.Adj a b → leftPotential a ≤ leftPotential b + 1 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem right_lipschitz : ∀ a b, H.Adj a b → rightPotential a ≤ rightPotential b + 1 := by decide

/-- Finite connectedness makes the eccentricity finite. -/
theorem dist_le_eccentricity_toNat (x y : Fin 31) : H.dist x y ≤ (H.eccent x).toNat := by
  obtain ⟨z,hz⟩ := H.exists_edist_eq_eccent_of_finite x
  have hfin : H.eccent x ≠ ⊤ := by
    rw [← hz]
    exact edist_ne_top_iff_reachable.mpr (connected x z)
  have he := ENat.toNat_le_toNat (H.edist_le_eccent (u := x) (v := y)) hfin
  exact he

/-- These two exact potentials certify the lower eccentricities in the manuscript. -/
theorem eccentricity_lower (x : Fin 31) : eccLower x ≤ (H.eccent x).toNat := by
  apply max_le
  · exact (potential_le_dist connected leftPotential left_lipschitz 27 (by decide) x).trans
      (dist_le_eccentricity_toNat x 27)
  · exact (potential_le_dist connected rightPotential right_lipschitz 0 (by decide) x).trans
      (dist_le_eccentricity_toNat x 0)

set_option maxRecDepth 1000000 in
theorem lower_sum : ∑ x : Fin 31, eccLower x = 114 := by decide

/-- The actual average eccentricity is at least 114/31, enough for the refutation. -/
theorem average_lower : (114 : ℝ) / 31 ≤ averageEccentricity H := by
  have hs : 114 ≤ ∑ x : Fin 31, (H.eccent x).toNat := by
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin 31))) => eccentricity_lower x)
    rwa [lower_sum] at hh
  unfold averageEccentricity
  norm_num only [Fintype.card_fin]
  have hsR : (114 : ℝ) ≤ (∑ x : Fin 31, (H.eccent x).toNat : ℕ) := by exact_mod_cast hs
  exact div_le_div_of_nonneg_right hsR (by norm_num)

end WOWII72
