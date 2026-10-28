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
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace WOWII72
open SimpleGraph Finset

def relation (i j : Fin 31) : Prop :=
  i.val ≠ j.val ∧
    ((i.val < 24 ∧ j.val < 24) ∨
     (i.val < 24 ∧ j.val = 24) ∨ (j.val < 24 ∧ i.val = 24) ∨
     (24 ≤ i.val ∧ i.val ≤ 26 ∧ j.val = i.val + 1) ∨
     (24 ≤ j.val ∧ j.val ≤ 26 ∧ i.val = j.val + 1) ∨
     (28 ≤ i.val ∧ 24 ≤ j.val ∧ j.val ≤ 26) ∨
     (28 ≤ j.val ∧ 24 ≤ i.val ∧ i.val ≤ 26))

def H : SimpleGraph (Fin 31) where
  Adj := relation
  symm := ⟨by intro i j hij; dsimp [relation] at *; omega⟩
  loopless := ⟨by intro i; simp [relation]⟩

instance : DecidableRel H.Adj := by
  intro i j
  unfold H relation
  infer_instance

def project (i : Fin 31) : Fin 8 :=
  ⟨if i.val < 24 then 0 else i.val - 23, by split_ifs <;> omega⟩

def embed (i : Fin 8) : Fin 31 :=
  ⟨if i.val = 0 then 0 else i.val + 23, by split_ifs <;> omega⟩

def small : SimpleGraph (Fin 8) := H.comap embed
instance : DecidableRel small.Adj := fun i j => inferInstanceAs (Decidable (H.Adj (embed i) (embed j)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem project_equal (i j : Fin 31) :
    project i = project j ↔ i = j ∨ (i.val < 24 ∧ j.val < 24) := by
  simp only [project, Fin.mk.injEq]
  by_cases hi : i.val < 24 <;> by_cases hj : j.val < 24 <;> simp [hi, hj] <;> omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem project_adj : ∀ i j : Fin 31, project i ≠ project j →
    (H.Adj i j ↔ small.Adj (project i) (project j)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem clique_exit : ∀ i j : Fin 31, i.val ≤ 24 → i ≠ 24 → H.Adj i j → j.val ≤ 24 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem clique_edges : ∀ i j : Fin 31, i.val < 24 → j.val < 24 → i ≠ j → H.Adj i j := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem clique_attachment : ∀ i : Fin 31, i.val < 24 → H.Adj i 24 := by decide

/-- An explicit finite obstruction: a triangle, a four-cycle, or an isolated vertex. -/
def Obstruction (s : Finset (Fin 8)) : Prop :=
  (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, small.Adj a b ∧ small.Adj b c ∧ small.Adj c a) ∨
  (∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s,
    a ≠ c ∧ b ≠ d ∧ small.Adj a b ∧ small.Adj b c ∧ small.Adj c d ∧ small.Adj d a) ∨
  (∃ a ∈ s, ∀ b ∈ s, ¬ small.Adj a b)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem small_obstruction : ∀ s : Finset (Fin 8), 5 < s.card → Obstruction s := by
  unfold Obstruction
  decide

end WOWII72
