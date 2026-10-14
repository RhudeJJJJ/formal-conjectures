/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII397cProof

namespace WOWII397cAudit
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def IsTwoDominating (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

noncomputable def twoDominationNumber : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

def supports : Finset V :=
  Finset.univ.filter fun s => ∃ p, G.degree p = 1 ∧ G.Adj p s

def square : SimpleGraph V where
  Adj v w := v ≠ w ∧ (G.Adj v w ∨ ∃ z, G.Adj v z ∧ G.Adj z w)
  symm := ⟨by
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | ⟨z,hz,hw⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨z,hw.symm,hz.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [DecidableEq V] in
theorem square_is_walk_square (u v : V) :
    (square G).Adj u v ↔ u ≠ v ∧ ∃ w : G.Walk u v, w.length ≤ 2 := by
  constructor
  · rintro ⟨hne,ha | ⟨z,hz,hw⟩⟩
    · exact ⟨hne,Walk.cons ha Walk.nil,by simp⟩
    · exact ⟨hne,Walk.cons hz (Walk.cons hw Walk.nil),by simp⟩
  · rintro ⟨hne,w,hw⟩
    refine ⟨hne,?_⟩
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons ha w =>
      cases w with
      | nil => exact Or.inl ha
      | cons hb w =>
        cases w with
        | nil => exact Or.inr ⟨_,ha,hb⟩
        | cons hc w => simp only [Walk.length_cons] at hw; omega

theorem exact_statement : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
      twoDominationNumber G ≤ (Finset.univ \ supports G).card + (square G).dominationNumber := by
  intro V _ _ G _ hG hn
  exact WOWII397cProof.conjecture397c G hG hn

#print axioms WOWII397cProof.square_dominates_supports
#print axioms WOWII397cProof.transport
#print axioms WOWII397cProof.no_adjacent_leaves
#print axioms WOWII397cProof.conjecture397c
#print axioms square_is_walk_square
#print axioms exact_statement
end WOWII397cAudit
