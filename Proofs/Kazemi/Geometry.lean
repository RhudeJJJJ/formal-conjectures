module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

/-! # Finite Boolean cubes: flips and common neighborhoods

Coordinate-free geometry for the exact Hamming-distance-one graph used in
Kazemi's conjecture. All neighborhoods in this module are open unless marked closed.
-/

@[expose] public section

namespace Kazemi.Certificate

open Finset

variable {ι : Type*} [DecidableEq ι]

abbrev Vertex (ι : Type*) := ι → Bool

def flip (x : Vertex ι) (i : ι) : Vertex ι := Function.update x i (!x i)

@[simp] theorem flip_self (x : Vertex ι) (i : ι) : flip x i i = !x i := by
  simp [flip]

@[simp] theorem flip_other (x : Vertex ι) {i j : ι} (h : j ≠ i) :
    flip x i j = x j := by simp [flip, h]

@[simp] theorem flip_twice (x : Vertex ι) (i : ι) : flip (flip x i) i = x := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem flip_ne (x : Vertex ι) (i : ι) : flip x i ≠ x := by
  intro h
  have := congrFun h i
  simp only [flip_self, Bool.not_eq_self] at this

theorem flip_injective (x : Vertex ι) : Function.Injective (flip x) := by
  intro i j h
  by_contra hn
  have hi := congrFun h i
  rw [flip_self, flip_other x hn] at hi
  simp only [Bool.not_eq_self] at hi

theorem flip_coordinate_injective (i : ι) : Function.Injective (fun x : Vertex ι => flip x i) := by
  intro x y h
  simpa using congrArg (fun z => flip z i) h

variable [Fintype ι]

def cube (ι : Type*) [Fintype ι] [DecidableEq ι] : SimpleGraph (Vertex ι) where
  Adj x y := (univ.filter fun i => x i ≠ y i).card = 1
  symm.symm x y h := by simpa only [ne_comm] using h
  loopless.irrefl x := by simp

instance : DecidableRel (cube ι).Adj := fun _ _ => inferInstanceAs (Decidable (_ = 1))

theorem adj_iff_flip (x y : Vertex ι) : (cube ι).Adj x y ↔ ∃ i, flip x i = y := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    have hxy : x i ≠ y i := by
      have : i ∈ univ.filter (fun j => x j ≠ y j) := by rw [hi]; simp
      simpa using this
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp only [flip_self]
      cases hxi : x i <;> cases hyi : y i <;> simp_all
    · rw [flip_other _ hj]
      by_contra hne
      have : j ∈ univ.filter (fun j => x j ≠ y j) := by simp [hne]
      rw [hi] at this
      exact hj (mem_singleton.mp this)
  · rintro ⟨i, rfl⟩
    change (univ.filter fun j => x j ≠ flip x i j).card = 1
    have hf : (univ.filter fun j => x j ≠ flip x i j) = {i} := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    rw [hf, card_singleton]

@[simp] theorem adj_flip (x : Vertex ι) (i : ι) : (cube ι).Adj x (flip x i) :=
  (adj_iff_flip _ _).2 ⟨i, rfl⟩

theorem adj_eq_flip_of_ne_at {x y : Vertex ι} (h : (cube ι).Adj x y)
    {i : ι} (hi : x i ≠ y i) : flip x i = y := by
  obtain ⟨j, rfl⟩ := (adj_iff_flip _ _).1 h
  by_cases hij : i = j
  · subst j; rfl
  · exact False.elim (hi (flip_other _ hij).symm)

theorem adj_flip_both (x y : Vertex ι) (i : ι) :
    (cube ι).Adj (flip x i) (flip y i) ↔ (cube ι).Adj x y := by
  change (univ.filter (fun j => flip x i j ≠ flip y i j)).card = 1 ↔ _
  have hf : (univ.filter (fun j => flip x i j ≠ flip y i j)) =
      univ.filter (fun j => x j ≠ y j) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [hf]; rfl

def neighbors (x : Vertex ι) : Finset (Vertex ι) := univ.filter ((cube ι).Adj x)

@[simp] theorem mem_neighbors {x y : Vertex ι} : y ∈ neighbors x ↔ (cube ι).Adj x y := by
  simp [neighbors]

theorem neighbors_eq_image (x : Vertex ι) : neighbors x = univ.image (flip x) := by
  ext y
  simp [adj_iff_flip]

@[simp] theorem card_neighbors (x : Vertex ι) : (neighbors x).card = Fintype.card ι := by
  rw [neighbors_eq_image, card_image_of_injective _ (flip_injective x), card_univ]

def closedBall (x : Vertex ι) : Finset (Vertex ι) := insert x (neighbors x)

@[simp] theorem mem_closedBall {x y : Vertex ι} :
    y ∈ closedBall x ↔ y = x ∨ (cube ι).Adj x y := by simp [closedBall]

theorem closedBall_symm (x y : Vertex ι) : y ∈ closedBall x ↔ x ∈ closedBall y := by
  simp only [mem_closedBall, eq_comm, (cube ι).adj_comm]

@[simp] theorem card_closedBall (x : Vertex ι) :
    (closedBall x).card = Fintype.card ι + 1 := by simp [closedBall]

def common (C : Finset (Vertex ι)) : Finset (Vertex ι) :=
  univ.filter fun x => ∀ y ∈ C, (cube ι).Adj x y

@[simp] theorem mem_common {C : Finset (Vertex ι)} {x : Vertex ι} :
    x ∈ common C ↔ ∀ y ∈ C, (cube ι).Adj x y := by simp [common]

theorem common_pair_subset {x y : Vertex ι} {i : ι} (hi : x i ≠ y i) :
    common {x,y} ⊆ {flip x i, flip y i} := by
  intro z hz
  have hx : (cube ι).Adj x z := ((mem_common.1 hz) x (by simp)).symm
  have hy : (cube ι).Adj y z := ((mem_common.1 hz) y (by simp)).symm
  by_cases hzi : z i = x i
  · have hiy : y i ≠ z i := by rw [hzi]; exact Ne.symm hi
    simp [adj_eq_flip_of_ne_at hy hiy]
  · simp [adj_eq_flip_of_ne_at hx (Ne.symm hzi)]

theorem common_pair_card_le_two {x y : Vertex ι} (hxy : x ≠ y) :
    (common {x,y}).card ≤ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  exact (card_le_card (common_pair_subset hi)).trans (card_insert_le _ _ |>.trans (by simp))

theorem common_mono {C D : Finset (Vertex ι)} (h : C ⊆ D) : common D ⊆ common C := by
  intro x hx
  exact mem_common.2 fun y hy => mem_common.1 hx y (h hy)

theorem common_card_le_one {C : Finset (Vertex ι)} (hC : 3 ≤ C.card) :
    (common C).card ≤ 1 := by
  apply card_le_one.2
  intro x hx y hy
  by_contra hxy
  have hs : C ⊆ common {x,y} := by
    intro z hz
    simp only [mem_common, mem_insert, mem_singleton]
    intro w hw
    rcases hw with rfl | rfl
    · exact (mem_common.1 hx z hz).symm
    · exact (mem_common.1 hy z hz).symm
  have := (card_le_card hs).trans (common_pair_card_le_two hxy)
  omega

end Kazemi.Certificate
