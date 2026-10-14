/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Tactic

namespace WOWII397cProof
open SimpleGraph
set_option maxHeartbeats 0
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def IsTwoDominating (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

noncomputable def twoDominationNumber : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

def supports : Finset V :=
  Finset.univ.filter fun s => ∃ p, G.degree p = 1 ∧ G.Adj p s

noncomputable def move (v : V) : V :=
  if h : G.degree v = 1 then (G.degree_eq_one_iff_existsUnique_adj.mp h).choose else v

omit [DecidableEq V] in
theorem move_leaf {p s : V} (hp : G.degree p = 1) (hs : G.Adj p s) : move G p = s := by
  classical
  unfold move
  rw [dif_pos hp]
  exact ((G.degree_eq_one_iff_existsUnique_adj.mp hp).choose_spec.2 s hs).symm

omit [DecidableEq V] in
theorem move_nonleaf {v : V} (h : G.degree v ≠ 1) : move G v = v := by
  classical
  simp [move,h]

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
theorem square_dominates_supports (D : Finset V) (hD : (square G).IsDominating D) :
    ∀ x ∈ supports G, x ∈ D ∨ ∃ z ∈ D, G.Adj x z := by
  intro x hx
  obtain ⟨p,hp,hpx⟩ := (Finset.mem_filter.mp hx).2
  have hu := (G.degree_eq_one_iff_existsUnique_adj.mp hp).choose_spec.2
  have uniq : ∀ z, G.Adj p z → z = x := by
    intro z hz
    exact (hu z hz).trans (hu x hpx).symm
  rcases hD p with hd | ⟨z,hz,hpz⟩
  · exact Or.inr ⟨p,hd,hpx.symm⟩
  · rcases hpz.2 with ha | ⟨w,hw,hwz⟩
    · exact Or.inl ((uniq z ha) ▸ hz)
    · exact Or.inr ⟨z,hz,(uniq w hw) ▸ hwz⟩

theorem transport
    (hn : ∀ p q, G.degree p = 1 → G.degree q = 1 → ¬ G.Adj p q)
    (D : Finset V) (hD : ∀ x ∈ supports G, x ∈ D ∨ ∃ z ∈ D, G.Adj x z) :
    ∃ Q : Finset V, IsTwoDominating G Q ∧
      Q.card ≤ (Finset.univ \ supports G).card + D.card := by
  classical
  let Q := (Finset.univ \ supports G) ∪ D.image (move G)
  refine ⟨Q, ?_, (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)⟩
  intro x hx
  have hxs : x ∈ supports G := by
    by_contra h
    exact hx (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩))
  obtain ⟨p,hp,hpx⟩ := (Finset.mem_filter.mp hxs).2
  have hpns : p ∉ supports G := by
    intro h
    obtain ⟨q,hq,hqp⟩ := (Finset.mem_filter.mp h).2
    exact hn q p hq hp hqp
  have hpQ : p ∈ Q := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hpns⟩)
  have hxD : x ∉ D := by
    intro h
    have hmove : move G x = x := by
      apply move_nonleaf
      intro hxl
      exact hn p x hp hxl hpx
    exact hx (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,h,hmove⟩))
  obtain ⟨z,hz,hxz⟩ := (hD x hxs).resolve_left hxD
  have hzn : G.degree z ≠ 1 := by
    intro h
    exact hx (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,move_leaf G h hxz.symm⟩))
  have hzQ : z ∈ Q := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,move_nonleaf G hzn⟩)
  have hne : p ≠ z := by intro h; subst z; exact hzn hp
  have hsub : {p,z} ⊆ Q.filter (fun w => G.Adj x w) := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hpQ,hpx.symm⟩
    · exact Finset.mem_filter.mpr ⟨hzQ,hxz⟩
  simpa [hne] using Finset.card_le_card hsub

theorem no_adjacent_leaves (hG : G.Connected) (hn : 2 < Fintype.card V) :
    ∀ p q, G.degree p = 1 → G.degree q = 1 → ¬ G.Adj p q := by
  intro p q hp hq hpq
  have up : ∀ z, G.Adj p z → z = q := by
    obtain ⟨s,_,hs⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hp
    intro z hz; exact (hs z hz).trans (hs q hpq).symm
  have uq : ∀ z, G.Adj q z → z = p := by
    obtain ⟨s,_,hs⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hq
    intro z hz; exact (hs z hz).trans (hs p hpq.symm).symm
  have walk_closed : ∀ {a b}, G.Walk a b → (a = p ∨ a = q) → (b = p ∨ b = q) := by
    intro a b w
    induction w with
    | nil => exact id
    | @cons a b c hab w ih =>
      intro ha
      apply ih
      rcases ha with rfl | rfl
      · exact Or.inr (up b hab)
      · exact Or.inl (uq b hab)
  have hsub : (Finset.univ : Finset V) ⊆ {p,q} := by
    intro v _
    obtain ⟨w⟩ := hG p v
    simpa only [Finset.mem_insert,Finset.mem_singleton] using walk_closed w (Or.inl rfl)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_le_two (a:=p) (b:=q))
  rw [Finset.card_univ] at hc
  omega

theorem conjecture397c (hG : G.Connected) (hn : 2 < Fintype.card V) :
    twoDominationNumber G ≤ (Finset.univ \ supports G).card + (square G).dominationNumber := by
  obtain ⟨D,hD,hcard⟩ := exists_isNDominatingSet_dominationNumber (square G)
  obtain ⟨Q,hQ,hcost⟩ := transport G (no_adjacent_leaves G hG hn) D
    (square_dominates_supports G D hD)
  have hnum : twoDominationNumber G ≤ Q.card := Nat.sInf_le ⟨Q,hQ,rfl⟩
  exact hnum.trans (hcard ▸ hcost)

#print axioms conjecture397c
end WOWII397cProof
