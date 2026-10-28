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
public import Proofs.WOWII9684.BFS
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace WOWII96
open SimpleGraph Finset
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def charge (hc : G.Connected) (r x : V) : V :=
  if Even (G.dist r x) then x else parent hc r x

omit [Fintype V] in
/-- Every charged index is in an even distance layer. -/
theorem charge_even (hc : G.Connected) (r x : V) : Even (G.dist r (charge hc r x)) := by
  classical
  by_cases he : Even (G.dist r x)
  · simp [charge, he]
  · have hx : x ≠ r := by intro hx; subst x; simp at he
    have hp := (parent_spec hc r x hx).2
    simp only [charge, if_neg he]
    simp only [Nat.even_iff] at he ⊢
    omega

omit [Fintype V] in
/-- A charged vertex is the index itself or a child one layer farther out. -/
theorem charge_cases (hc : G.Connected) (r p x : V) (hx : charge hc r x = p) :
    x = p ∨ (G.Adj p x ∧ G.dist r x = G.dist r p + 1) := by
  classical
  by_cases he : Even (G.dist r x)
  · left; simpa [charge, he] using hx
  · right
    have hxr : x ≠ r := by intro hxr; subst x; simp at he
    have hp := parent_spec hc r x hxr
    have hparent : parent hc r x = p := by simpa [charge, he] using hx
    simpa [hparent] using And.intro hp.1.symm hp.2.symm

open scoped Classical in
/-- The non-root fibre costs at most one fewer than maximum local independence. -/
theorem fibre_bound (hc : G.Connected) (r : V) (I : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (M : ℕ)
    (hM : ∀ v, indepNeighborsCard G v ≤ M) (hM2 : 2 ≤ M)
    (p : V) :
    (I.filter (fun x => charge hc r x = p)).card ≤
      M - 1 + if p = r then 1 else 0 := by
  classical
  let F := I.filter (fun x => charge hc r x = p)
  have hFI : ∀ x ∈ F, x ∈ I := fun x hx => (Finset.mem_filter.mp hx).1
  have hcases : ∀ x ∈ F, x = p ∨ (G.Adj p x ∧ G.dist r x = G.dist r p + 1) := by
    intro x hx
    exact charge_cases hc r p x (Finset.mem_filter.mp hx).2
  have hInd : G.IsIndepSet (F : Set V) := by
    intro x hx y hy hxy
    exact hI (hFI x hx) (hFI y hy) hxy
  by_cases hpI : p ∈ I
  · have hsub : F ⊆ {p} := by
      intro x hx
      rcases hcases x hx with hxp | hxp
      · simpa using hxp
      · exact (hI hpI (hFI x hx) hxp.1.ne hxp.1).elim
    have hb : F.card ≤ 1 := by simpa using Finset.card_le_card hsub
    change F.card ≤ _
    split_ifs <;> omega
  · have hchild : ∀ x ∈ F, G.Adj p x ∧ G.dist r x = G.dist r p + 1 := by
      intro x hx
      rcases hcases x hx with hxp | hxp
      · exact (hpI (hxp ▸ hFI x hx)).elim
      · exact hxp
    by_cases hpr : p = r
    · have hb := (local_card_bound p F hInd (fun x hx => (hchild x hx).1)).trans (hM p)
      change F.card ≤ _
      rw [if_pos hpr]
      omega
    · obtain ⟨hq, hqd⟩ := parent_spec hc r p hpr
      let q := parent hc r p
      have hqF : q ∉ F := by
        intro hqF
        have hd := (hchild q hqF).2
        change G.dist r q + 1 = G.dist r p at hqd
        omega
      have hnonadj : ∀ x ∈ F, ¬ G.Adj q x := by
        intro x hx hadj
        have hd := (hchild x hx).2
        have ht := hc.dist_triangle (u := r) (v := q) (w := x)
        have hd1 := G.dist_eq_one_iff_adj.mpr hadj
        change G.dist r q + 1 = G.dist r p at hqd
        omega
      have hIns : G.IsIndepSet ((insert q F : Finset V) : Set V) := by
        intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · exact hnonadj y hy
        · rcases hy with rfl | hy
          · exact fun ha => hnonadj x hx ha.symm
          · exact hInd hx hy hxy
      have hn : ∀ x ∈ insert q F, G.Adj p x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hq
        · exact (hchild x hx).1
      have hb := (local_card_bound p (insert q F) hIns hn).trans (hM p)
      rw [Finset.card_insert_of_notMem hqF] at hb
      change F.card ≤ _
      rw [if_neg hpr]
      omega

/-- Counting the fibres gives the global independent-set bound at every root. -/
theorem independent_bound (hc : G.Connected) (r : V) (I : Finset V)
    (hI : G.IsIndepSet (I : Set V)) (M : ℕ)
    (hM : ∀ v, indepNeighborsCard G v ≤ M) (hM2 : 2 ≤ M) :
    I.card ≤ 1 + (Finset.univ.filter (fun p => Even (G.dist r p))).card * (M - 1) := by
  classical
  let E := Finset.univ.filter (fun p => Even (G.dist r p))
  have hr : r ∈ E := by simp [E]
  have hmap : (I : Set V).MapsTo (charge hc r) E := by
    intro x _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, charge_even hc r x⟩
  calc I.card = ∑ p ∈ E, (I.filter (fun x => charge hc r x = p)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ p ∈ E, (M - 1 + if p = r then 1 else 0) := by
      apply Finset.sum_le_sum
      intro p _
      exact fibre_bound hc r I hI M hM hM2 p
    _ = 1 + E.card * (M - 1) := by
      simp [Finset.sum_add_distrib, hr, Nat.add_comm]

end WOWII96
