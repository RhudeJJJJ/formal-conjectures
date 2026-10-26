module

public import Proofs.Kazemi.CubeCounting
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-! # The two-extra-colors lower bound

Active color classes are those with a common open neighbor. Their representatives
form a total dominating set. Capacity counting excludes a coloring with at most
one inactive class; equality in the independent-set matching bound handles Q5.
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def fiber (c : Vertex ι → Fin k) (i : Fin k) : Finset (Vertex ι) :=
  univ.filter fun x => c x = i

@[simp] theorem mem_fiber {c : Vertex ι → Fin k} {i : Fin k} {x : Vertex ι} :
    x ∈ fiber c i ↔ c x = i := by simp [fiber]

def activeColors (c : Vertex ι → Fin k) : Finset (Fin k) :=
  univ.filter fun i => (common (fiber c i)).Nonempty

@[simp] theorem mem_activeColors {c : Vertex ι → Fin k} {i : Fin k} :
    i ∈ activeColors c ↔ (common (fiber c i)).Nonempty := by simp [activeColors]

theorem sum_fiber_card (c : Vertex ι → Fin k) (T : Finset (Fin k)) :
    ∑ i ∈ T, (fiber c i).card = (univ.filter fun x => c x ∈ T).card := by
  exact sum_card_fiberwise_eq_card_filter univ T c

theorem sum_all_fiber_card (c : Vertex ι → Fin k) :
    ∑ i : Fin k, (fiber c i).card = Fintype.card (Vertex ι) := by
  simpa using sum_fiber_card c univ

theorem fiber_independent (c : Vertex ι → Fin k)
    (hproper : ∀ x y, (cube ι).Adj x y → c x ≠ c y) (i : Fin k) : Independent (fiber c i) := by
  intro x hx y hy hxy
  exact hproper x y hxy ((mem_fiber.1 hx).trans (mem_fiber.1 hy).symm)

theorem active_representatives_bound (c : Vertex ι → Fin k) (hsurj : Function.Surjective c)
    (hdom : ∀ v, ∃ i, ∀ w, c w = i → (cube ι).Adj v w)
    (g : ℕ) (hgamma : ∀ S : Finset (Vertex ι), TotallyDominates S → g ≤ S.card) :
    g ≤ (activeColors c).card := by
  classical
  let r : Fin k → Vertex ι := fun i => Classical.choose (hsurj i)
  have hr : ∀ i, c (r i) = i := fun i => Classical.choose_spec (hsurj i)
  have hinj : Function.Injective r := by
    intro i j he
    have h := congrArg c he
    simpa only [hr] using h
  have hT : TotallyDominates ((activeColors c).image r) := by
    intro v
    obtain ⟨i, hi⟩ := hdom v
    have hcv : v ∈ common (fiber c i) := mem_common.2 fun w hw => hi w (mem_fiber.1 hw)
    refine ⟨r i, mem_image.2 ⟨i, mem_activeColors.2 ⟨v, hcv⟩, rfl⟩, hi (r i) (hr i)⟩
  have := hgamma _ hT
  simpa only [card_image_of_injective _ hinj] using this

theorem active_cover_count (c : Vertex ι → Fin k)
    (hdom : ∀ v, ∃ i, ∀ w, c w = i → (cube ι).Adj v w) :
    Fintype.card (Vertex ι) ≤ ∑ i ∈ activeColors c, (common (fiber c i)).card := by
  have he : (activeColors c).biUnion (fun i => common (fiber c i)) = univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨i, hi⟩ := hdom v
    have hc : v ∈ common (fiber c i) := mem_common.2 fun w hw => hi w (mem_fiber.1 hw)
    exact mem_biUnion.2 ⟨i, mem_activeColors.2 ⟨v, hc⟩, hc⟩
  have h := card_biUnion_le (s := activeColors c) (t := fun i => common (fiber c i))
  rwa [he, card_univ] at h

theorem active_capacity_count (c : Vertex ι → Fin k) (hsurj : Function.Surjective c)
    (hd : 3 ≤ Fintype.card ι) :
    (∑ i ∈ activeColors c, (fiber c i).card) +
      (∑ i ∈ activeColors c, (common (fiber c i)).card) ≤
        (Fintype.card ι + 1) * (activeColors c).card := by
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ _i ∈ activeColors c, (Fintype.card ι + 1) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨x, hx⟩ := hsurj i
      exact common_capacity hd ⟨x, mem_fiber.2 hx⟩ (mem_activeColors.1 hi)
    _ = _ := by simp [Nat.mul_comm]

variable [Nonempty ι]

theorem coloring_lower_bound (c : Vertex ι → Fin k)
    (hproper : ∀ x y, (cube ι).Adj x y → c x ≠ c y)
    (hsurj : Function.Surjective c)
    (hdom : ∀ v, ∃ i, ∀ w, c w = i → (cube ι).Adj v w)
    (g : ℕ) (hd : 5 ≤ Fintype.card ι) (hg : Fintype.card ι + 1 ≤ g)
    (hN : Fintype.card (Vertex ι) + g = Fintype.card ι * g)
    (hgamma : ∀ S : Finset (Vertex ι), TotallyDominates S → g ≤ S.card) :
    g + 2 ≤ k := by
  classical
  let A := activeColors c
  let d := Fintype.card ι
  let N := Fintype.card (Vertex ι)
  have hactive : g ≤ A.card := active_representatives_bound c hsurj hdom g hgamma
  have hcover := active_cover_count c hdom
  have hcap := active_capacity_count c hsurj (by omega : 3 ≤ Fintype.card ι)
  by_contra hbudget
  have hk : k ≤ g + 1 := by omega
  by_cases hall : A = univ
  · have ha : A.card = k := by rw [hall, card_univ, Fintype.card_fin]
    have hclasses : (∑ i ∈ activeColors c, (fiber c i).card) = N := by
      change (∑ i ∈ A, (fiber c i).card) = N
      rw [hall]
      exact sum_all_fiber_card c
    rw [hclasses] at hcap
    change N ≤ _ at hcover
    change _ ≤ (d + 1) * A.card at hcap
    rw [ha] at hcap
    have hbound : 2 * N ≤ (d + 1) * (g + 1) :=
      (by omega : 2 * N ≤ (d + 1) * k).trans (Nat.mul_le_mul_left (d + 1) hk)
    have hdim : 5 * g ≤ d * g := Nat.mul_le_mul_right g hd
    change N + g = d * g at hN
    change d + 1 ≤ g at hg
    nlinarith
  · have hex : ∃ j, j ∉ A := by
      by_contra hn
      have hforall : ∀ j, j ∈ A := by simpa only [not_exists, not_not] using hn
      exact hall (eq_univ_of_forall hforall)
    obtain ⟨j, hj⟩ := hex
    have hs : A ⊆ univ.erase j := by
      intro i hi
      exact mem_erase.2 ⟨by intro h; subst i; exact hj hi, mem_univ _⟩
    have herase : (univ.erase j : Finset (Fin k)).card = k - 1 := by simp
    have hsize := card_le_card hs
    rw [herase] at hsize
    have hjlt := j.isLt
    have ha : A.card = g := by omega
    have hk' : k = g + 1 := by omega
    have he : A = univ.erase j := eq_of_subset_of_card_le hs (by rw [herase, ha, hk']; omega)
    let R := fiber c j
    have hR : Independent R := fiber_independent c hproper j
    have hhalf : R.card ≤ Rᶜ.card := independent_le_compl (Classical.choice ‹Nonempty ι›) hR
    have hpart : R.card + Rᶜ.card = N := card_add_card_compl R
    have hclasses : (∑ i ∈ activeColors c, (fiber c i).card) = Rᶜ.card := by
      rw [sum_fiber_card]
      change (univ.filter fun x => c x ∈ A).card = Rᶜ.card
      rw [he]
      congr 1
      ext x
      simp [R, fiber]
    rw [hclasses] at hcap
    change _ ≤ (d + 1) * A.card at hcap
    rw [ha] at hcap
    change N ≤ _ at hcover
    have hbound : 3 * N ≤ 2 * ((d + 1) * g) := by omega
    change N + g = d * g at hN
    have hd5 : d = 5 := by
      by_contra hn
      have hd6 : 6 ≤ d := by omega
      have hmul : 6 * g ≤ d * g := Nat.mul_le_mul_right g hd6
      change d + 1 ≤ g at hg
      nlinarith
    have hsame : R.card = Rᶜ.card := by rw [hd5] at hN hcap; omega
    have hcomp : Independent Rᶜ := independent_compl_of_card_eq hR hsame
    have hpos : 0 < Rᶜ.card := by rw [hd5] at hN; change d + 1 ≤ g at hg; omega
    obtain ⟨v, hv⟩ := card_pos.1 hpos
    obtain ⟨i, hi⟩ := hdom v
    have hci : v ∈ common (fiber c i) := mem_common.2 fun w hw => hi w (mem_fiber.1 hw)
    have hiA : i ∈ A := mem_activeColors.2 ⟨v, hci⟩
    have hij : i ≠ j := by intro h; subst i; exact hj hiA
    obtain ⟨w, hw⟩ := hsurj i
    have hwc : w ∈ Rᶜ := by
      apply mem_compl.2
      intro hwr
      exact hij (hw.symm.trans (mem_fiber.1 hwr))
    exact hcomp v hv w hwc (hi w hw)

end Kazemi.Certificate
