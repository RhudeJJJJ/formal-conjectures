module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The one-unit spectral count bound for a difference of two rank-one forms.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Lemma 2.1.
-/
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.CountGap

open Finset
open scoped InnerProductSpace
noncomputable section

variable {I : Type*} [Fintype I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def extend (α : I → ℝ) (t : ℝ) : ({i : I // t < α i} → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun c i := if hi : t < α i then c ⟨i, hi⟩ else 0
  map_add' c d := by ext i; dsimp; split_ifs <;> simp
  map_smul' r c := by ext i; dsimp; split_ifs <;> simp

def embed (e : OrthonormalBasis I ℝ E) (α : I → ℝ) (t : ℝ) :
    ({i : I // t < α i} → ℝ) →ₗ[ℝ] E :=
  e.repr.symm.toLinearEquiv.toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℝ (I → ℝ)).symm.toLinearMap ∘ₗ extend α t

theorem embed_coordinates (e : OrthonormalBasis I ℝ E) (α : I → ℝ) (t : ℝ)
    (c : {i : I // t < α i} → ℝ) (i : I) :
    e.repr (embed e α t c) i = if hi : t < α i then c ⟨i, hi⟩ else 0 := by
  simp [embed, extend]

theorem embed_injective (e : OrthonormalBasis I ℝ E) (α : I → ℝ) (t : ℝ) :
    Function.Injective (embed e α t) := by
  intro c d h
  funext i
  have hh := congrArg (fun x : E => e.repr x i) h
  simpa only [embed_coordinates, dif_pos i.property] using hh

theorem quadratic_coordinates (T : E →ₗ[ℝ] E) (e : OrthonormalBasis I ℝ E)
    (α : I → ℝ) (hdiag : ∀ x i, e.repr (T x) i = α i * e.repr x i) (t : ℝ) (x : E) :
    ⟪x, T x⟫_ℝ - t * ‖x‖ ^ 2 = ∑ i, (α i - t) * (e.repr x i) ^ 2 := by
  have hnorm : ‖x‖ ^ 2 = ∑ i, (e.repr x i) ^ 2 := by
    rw [← e.repr.norm_map x, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hnorm, ← e.repr.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, hdiag]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem positive_on_embed (T : E →ₗ[ℝ] E) (e : OrthonormalBasis I ℝ E)
    (α : I → ℝ) (hdiag : ∀ x i, e.repr (T x) i = α i * e.repr x i)
    (t : ℝ) (c : {i : I // t < α i} → ℝ) (hc : c ≠ 0) :
    0 < ⟪embed e α t c, T (embed e α t c)⟫_ℝ - t * ‖embed e α t c‖ ^ 2 := by
  rw [quadratic_coordinates T e α hdiag t, Finset.sum_pos_iff_of_nonneg]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra! h
      exact hc (funext h)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [embed_coordinates, dif_pos i.property]
    exact mul_pos (sub_pos.mpr i.property) (sq_pos_of_ne_zero hi)
  · intro i _
    rw [embed_coordinates]
    split_ifs with hi
    · exact mul_nonneg (sub_nonneg.mpr hi.le) (sq_nonneg _)
    · simp

theorem nonpositive_without_high_coordinates (T : E →ₗ[ℝ] E)
    (e : OrthonormalBasis I ℝ E) (α : I → ℝ)
    (hdiag : ∀ x i, e.repr (T x) i = α i * e.repr x i) (t : ℝ) (x : E)
    (hx : ∀ i, t < α i → e.repr x i = 0) :
    ⟪x, T x⟫_ℝ - t * ‖x‖ ^ 2 ≤ 0 := by
  rw [quadratic_coordinates T e α hdiag t]
  apply Finset.sum_nonpos
  intro i _
  by_cases hi : t < α i
  · rw [hx i hi]; simp
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hi)) (sq_nonneg _)

/-- A single linear functional controls the positive part of the perturbation.
The comparison is proved by an injective map into the other high spectrum plus ℝ. -/
theorem count_le_add_one (S T : E →ₗ[ℝ] E) (eS eT : OrthonormalBasis I ℝ E)
    (α β : I → ℝ) (hS : ∀ x i, eS.repr (S x) i = α i * eS.repr x i)
    (hT : ∀ x i, eT.repr (T x) i = β i * eT.repr x i)
    (a : E →ₗ[ℝ] ℝ) (hform : ∀ x, a x = 0 → ⟪x, S x⟫_ℝ ≤ ⟪x, T x⟫_ℝ)
    (t : ℝ) :
    Fintype.card {i : I // t < α i} ≤ Fintype.card {i : I // t < β i} + 1 := by
  let J := {i : I // t < β i}
  let H : E →ₗ[ℝ] (J → ℝ) :=
    LinearMap.pi (fun i : J => (LinearMap.proj (i : I)).comp
      ((WithLp.linearEquiv 2 ℝ (I → ℝ)).toLinearMap.comp eT.repr.toLinearEquiv.toLinearMap))
  let F : ({i : I // t < α i} → ℝ) →ₗ[ℝ] ((J → ℝ) × ℝ) :=
    (H.prod a).comp (embed eS α t)
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply (LinearMap.ker_eq_bot').mpr
    intro c hc
    by_contra hc0
    have hH : H (embed eS α t c) = 0 := congrArg Prod.fst hc
    have ha : a (embed eS α t c) = 0 := congrArg Prod.snd hc
    have hh : ∀ i, t < β i → eT.repr (embed eS α t c) i = 0 := by
      intro i hi
      exact congrFun hH ⟨i, hi⟩
    have hp := positive_on_embed S eS α hS t c hc0
    have hn := nonpositive_without_high_coordinates T eT β hT t _ hh
    have hst := hform _ ha
    linarith
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Module.finrank_prod] using hd

#print axioms count_le_add_one

end
end Gebendorfer.RadenkovicGutman.CountGap
