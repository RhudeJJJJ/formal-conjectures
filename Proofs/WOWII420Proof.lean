/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import Proofs.TriangleCountProof
import Mathlib.Tactic

/-! Finite counterexamples to the source-note-determined upper-bound reconstruction
of WOWII420b/c. The raw archive has missing comparison glyphs. Written source:
Jonas J. Gebendorfer, A Common Counterexample Family for Two Graffiti.pc Bounds
on Independent Domination, 1 September2026. We certify W8, not family minimality. -/
namespace WOWII420Proof
open SimpleGraph Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V]

def neighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ I, G.Adj u v

def leaves (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 1

def minVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree v ≤ G.degree w

def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (I : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ I).card

/-- An incident triangle is uniquely determined by its opposite edge. -/
def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  edgesOn G (G.neighborFinset v)

def minTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, trianglesAt G v ≤ trianglesAt G w

def residual (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ \ neighborhood G (neighborhood G (leaves G))

def closedMinimum (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  minVertices G ∪ neighborhood G (minVertices G)

noncomputable def sourceMinTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, G.numTrianglesAtVertex v ≤ G.numTrianglesAtVertex w

lemma sourceMinTriangles_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    sourceMinTriangles G = minTriangles G := by
  classical
  ext v
  simp only [sourceMinTriangles, minTriangles, mem_filter, mem_univ, true_and]
  simp only [← TriangleCountProof.triangle_count, trianglesAt, edgesOn]

noncomputable def bound420b (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.induce (residual G : Set V)).indepNum + 4 * ((edgesOn G (closedMinimum G) : ℤ) - 1)
noncomputable def bound420c (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (G.induce (residual G : Set V)).indepNum + 4 * (((sourceMinTriangles G).card : ℤ) - 1)

/-- 0,1 are the adjacent supports; 2,3 are leaves. Each consecutive wing pair
has its support as third vertex of a triangle. -/
def witness : SimpleGraph (Fin 36) where
  Adj u v := u ≠ v ∧
    ((u = 0 ∧ (v = 1 ∨ v = 2 ∨ (4 ≤ v.val ∧ v.val < 20))) ∨
     (v = 0 ∧ (u = 1 ∨ u = 2 ∨ (4 ≤ u.val ∧ u.val < 20))) ∨
     (u = 1 ∧ (v = 3 ∨ 20 ≤ v.val)) ∨
     (v = 1 ∧ (u = 3 ∨ 20 ≤ u.val)) ∨
     (4 ≤ u.val ∧ 4 ≤ v.val ∧ u.val / 2 = v.val / 2))
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h|h|h|h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2.symm⟩)))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance : DecidableRel witness.Adj :=
  inferInstanceAs (DecidableRel fun u v : Fin 36 => u ≠ v ∧
    ((u = 0 ∧ (v = 1 ∨ v = 2 ∨ (4 ≤ v.val ∧ v.val < 20))) ∨
     (v = 0 ∧ (u = 1 ∨ u = 2 ∨ (4 ≤ u.val ∧ u.val < 20))) ∨
     (u = 1 ∧ (v = 3 ∨ 20 ≤ v.val)) ∨
     (v = 1 ∧ (u = 3 ∨ 20 ≤ u.val)) ∨
     (4 ≤ u.val ∧ 4 ≤ v.val ∧ u.val / 2 = v.val / 2)))

def parent (v : Fin 36) : Fin 36 :=
  if v = 0 then 0 else if v = 1 ∨ v = 2 ∨ (4 ≤ v.val ∧ v.val < 20) then 0 else 1
lemma parent_adj : ∀ v : Fin 36, v ≠ 0 → witness.Adj v (parent v) := by decide
lemma root_reachable (v : Fin 36) : witness.Reachable v 0 := by
  by_cases h0 : v = 0
  · subst v; exact .refl _
  have h := (parent_adj v h0).reachable
  by_cases hp : parent v = 0
  · simpa [hp] using h
  · have hp1 : parent v = 1 := by simp only [parent] at hp ⊢; split_ifs <;> simp_all
    exact h.trans (hp1 ▸ (show witness.Adj (1 : Fin 36) 0 by decide).reachable)
theorem witness_connected : witness.Connected :=
  ⟨fun u v => (root_reachable u).trans (root_reachable v).symm⟩

/-- Ten disjoint reservations: one vertex from each wing and two named vertices. -/
def reserve (mode : Fin 3) (j : Fin 10) : Finset (Fin 36) :=
  if hj : j.val < 8 then
    if mode = 0 then {⟨20 + 2*j.val, by omega⟩, ⟨21 + 2*j.val, by omega⟩}
    else {⟨4 + 2*j.val, by omega⟩, ⟨5 + 2*j.val, by omega⟩}
  else if j = 8 then {if mode = 0 then 0 else 2} else {if mode = 1 then 1 else 3}
lemma reserve_disjoint : ∀ (mode : Fin 3) (i j : Fin 10) (v : Fin 36),
    v ∈ reserve mode i → v ∈ reserve mode j → i = j := by decide

lemma reservations_bound (D : Finset (Fin 36)) (mode : Fin 3)
    (h : ∀ j : Fin 10, ∃ v ∈ D, v ∈ reserve mode j) : 10 ≤ D.card := by
  classical
  choose f hfD hfr using h
  let g : Fin 10 → {v // v ∈ D} := fun j => ⟨f j, hfD j⟩
  have hg : Function.Injective g := by
    intro i j hij
    have hh : f i = f j := congrArg Subtype.val hij
    exact reserve_disjoint mode i j (f i) (hfr i) (hh ▸ hfr j)
  simpa using Fintype.card_le_of_injective g hg

lemma leaf_forced {D : Finset (Fin 36)} (hD : witness.IsDominating (D : Set (Fin 36)))
    {p s : Fin 36} (hp : ∀ v, witness.Adj p v → v = s) (hs : s ∉ D) : p ∈ D := by
  rcases hD p with h | ⟨v, hv, he⟩
  · exact h
  · exact (hs ((hp v he) ▸ hv)).elim

lemma wing_hit {D : Finset (Fin 36)} (hD : witness.IsDominating (D : Set (Fin 36)))
    {p q s : Fin 36} (hp : ∀ v, witness.Adj p v → v = s ∨ v = q)
    (hs : s ∉ D) : p ∈ D ∨ q ∈ D := by
  rcases hD p with h | ⟨v, hv, he⟩
  · exact Or.inl h
  · rcases hp v he with rfl | rfl
    · exact (hs hv).elim
    · exact Or.inr hv

def leftA (j : Fin 8) : Fin 36 := ⟨4+2*j.val, by omega⟩
def leftB (j : Fin 8) : Fin 36 := ⟨5+2*j.val, by omega⟩
def rightA (j : Fin 8) : Fin 36 := ⟨20+2*j.val, by omega⟩
def rightB (j : Fin 8) : Fin 36 := ⟨21+2*j.val, by omega⟩
lemma left_wing_neighbors : ∀ (j : Fin 8) (v : Fin 36),
    witness.Adj (leftA j) v → v = 0 ∨ v = leftB j := by decide
lemma right_wing_neighbors : ∀ (j : Fin 8) (v : Fin 36),
    witness.Adj (rightA j) v → v = 1 ∨ v = rightB j := by decide

/-- A structural lower bound over arbitrary candidate sets; no powerset enumeration. -/
theorem independent_dominating_lower (D : Finset (Fin 36))
    (hD : witness.IsIndepDominating (D : Set (Fin 36))) : 10 ≤ D.card := by
  classical
  by_cases hs : (0 : Fin 36) ∈ D
  · have ht : (1 : Fin 36) ∉ D := by
      intro ht
      exact hD.1 hs ht (by decide) (by decide)
    have hq : (3 : Fin 36) ∈ D := leaf_forced (p := 3) (s := 1) hD.2 (by decide) ht
    apply reservations_bound D 0
    intro j
    by_cases hj : j.val < 8
    · let p : Fin 36 := ⟨20+2*j.val, by omega⟩
      let q : Fin 36 := ⟨21+2*j.val, by omega⟩
      have hp : ∀ v, witness.Adj p v → v = 1 ∨ v = q := by
        exact right_wing_neighbors ⟨j.val, hj⟩
      rcases wing_hit hD.2 hp ht with h | h
      · exact ⟨p, h, by simp [reserve, hj, p]⟩
      · exact ⟨q, h, by simp [reserve, hj, q]⟩
    · by_cases hj8 : j = 8
      · exact ⟨0, hs, by simp [reserve, hj8]⟩
      · exact ⟨3, hq, by simp [reserve, hj, hj8]⟩
  · have hp : (2 : Fin 36) ∈ D := leaf_forced (p := 2) (s := 0) hD.2 (by decide) hs
    by_cases ht : (1 : Fin 36) ∈ D
    · apply reservations_bound D 1
      intro j
      by_cases hj : j.val < 8
      · let p : Fin 36 := ⟨4+2*j.val, by omega⟩
        let q : Fin 36 := ⟨5+2*j.val, by omega⟩
        have hp' : ∀ v, witness.Adj p v → v = 0 ∨ v = q := by
          exact left_wing_neighbors ⟨j.val, hj⟩
        rcases wing_hit hD.2 hp' hs with h | h
        · exact ⟨p, h, by simp [reserve, hj, p]⟩
        · exact ⟨q, h, by simp [reserve, hj, q]⟩
      · by_cases hj8 : j = 8
        · exact ⟨2, hp, by simp [reserve, hj8]⟩
        · exact ⟨1, ht, by simp [reserve, hj, hj8]⟩
    · have hq : (3 : Fin 36) ∈ D := leaf_forced (p := 3) (s := 1) hD.2 (by decide) ht
      apply reservations_bound D 2
      intro j
      by_cases hj : j.val < 8
      · let p : Fin 36 := ⟨4+2*j.val, by omega⟩
        let q : Fin 36 := ⟨5+2*j.val, by omega⟩
        have hp' : ∀ v, witness.Adj p v → v = 0 ∨ v = q := by
          exact left_wing_neighbors ⟨j.val, hj⟩
        rcases wing_hit hD.2 hp' hs with h | h
        · exact ⟨p, h, by simp [reserve, hj, p]⟩
        · exact ⟨q, h, by simp [reserve, hj, q]⟩
      · by_cases hj8 : j = 8
        · exact ⟨2, hp, by simp [reserve, hj8]⟩
        · exact ⟨3, hq, by simp [reserve, hj, hj8]⟩

def selected : Finset (Fin 36) := {0,3,20,22,24,26,28,30,32,34}
lemma selected_certificate : witness.IsIndepDominating (selected : Set (Fin 36)) ∧
    selected.card = 10 := by
  constructor
  · change (∀ u ∈ selected, ∀ v ∈ selected, u ≠ v → ¬witness.Adj u v) ∧
      (∀ v, v ∈ selected ∨ ∃ w ∈ selected, witness.Adj v w)
    decide
  · decide

theorem independent_domination_eq : witness.indepDominationNumber = 10 := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨selected, selected_certificate.1.1, selected_certificate.1.2,
      selected_certificate.2⟩
  · apply le_csInf
    · exact ⟨10, selected, selected_certificate.1.1, selected_certificate.1.2,
        selected_certificate.2⟩
    · rintro n ⟨D, hD⟩
      rw [← hD.card_eq]
      exact independent_dominating_lower D ⟨hD.isIndep, hD.isDominating⟩

lemma residual_empty : residual witness = ∅ := by decide
lemma closedMinimum_spec : closedMinimum witness = {0,1,2,3} := by decide
lemma induced_edge_count : edgesOn witness (closedMinimum witness) = 3 := by
  rw [closedMinimum_spec]
  decide
lemma minimum_triangles : minTriangles witness = {2,3} := by decide

lemma residual_independence : (witness.induce (residual witness : Set (Fin 36))).indepNum = 0 := by
  rw [residual_empty]
  rw [indep_num_eq_computable]
  decide

theorem bound420b_eq : bound420b witness = 8 := by
  rw [bound420b, residual_independence, induced_edge_count]
  norm_num

theorem bound420c_eq : bound420c witness = 4 := by
  rw [bound420c, residual_independence, sourceMinTriangles_eq, minimum_triangles]
  have hc : ({2,3} : Finset (Fin 36)).card = 2 := by decide
  rw [hc]
  norm_num

theorem conjecture420b : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      (G.indepDominationNumber : ℤ) ≤ bound420b G := by
  intro h
  have hh := h (Fin 36) witness witness_connected (by decide)
  rw [independent_domination_eq, bound420b_eq] at hh
  norm_num at hh

theorem conjecture420c : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      (G.indepDominationNumber : ℤ) ≤ bound420c G := by
  intro h
  have hh := h (Fin 36) witness witness_connected (by decide)
  rw [independent_domination_eq, bound420c_eq] at hh
  norm_num at hh
end WOWII420Proof
