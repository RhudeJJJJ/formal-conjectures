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
public import Proofs.WOWII72.Tree
public import Proofs.WOWII72.Eccentricity
public import Proofs.WOWII9684.BFS
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section
namespace WOWII72
open SimpleGraph Finset

/-- Four explicit independent neighbours of vertex24. -/
theorem local_independence_lower : 4 ≤ indepNeighborsCard H 24 := by
  let s : Finset (Fin 31) := {0,28,29,30}
  have hs : H.IsIndepSet (s : Set (Fin 31)) := by decide
  have hn : ∀ x ∈ s, H.Adj 24 x := by decide
  have hb := WOWII96.local_card_bound 24 s hs hn
  have hcard : s.card = 4 := by decide
  rwa [hcard] at hb

/-- The submitted positive inequality fails on the actual 31-vertex graph. -/
theorem finite_refutation :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard H v)).max' (by simp)
    ¬ (⌈averageEccentricity H + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize H : ℝ)) := by
  classical
  dsimp only
  let M := (Finset.univ.image (fun v => indepNeighborsCard H v)).max' (by simp)
  have hm : 4 ≤ M := local_independence_lower.trans
    (Finset.le_max' _ _ (Finset.mem_image.mpr ⟨24,Finset.mem_univ _,rfl⟩))
  have hmR : (4 : ℝ) ≤ M := by exact_mod_cast hm
  have htR : (largestInducedTreeSize H : ℝ) ≤ 5 := by exact_mod_cast tree_upper
  have ha := average_lower
  have hceil := Int.le_ceil (averageEccentricity H + (M : ℝ) / 3)
  intro hb
  change (⌈averageEccentricity H + (M : ℝ) / 3⌉ : ℝ) ≤ _ at hb
  linarith

/-- Full negation of the original universal assertion for nontrivial finite graphs.
Every order at least two is represented as n+2. No restriction to a special
family is imposed on the universally quantified graph. -/
theorem full_conjecture72 :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 2))), G.Connected →
      let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
      ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ) := by
  intro h
  exact finite_refutation (h 29 H connected)

end WOWII72
