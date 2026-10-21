/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReducedDirectedIdentity
import Proofs.RadenkovicGutmanEscapeReducedReserveIdentity
namespace Gebendorfer.RadenkovicGutman.ReducedEscapeForms
open Set
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem directedCore_nonneg (h x a b : ℝ) (hh : h ∈ Ioc (0 : ℝ) (1/46))
    (hx : x ∈ Icc (653/2000 : ℝ) 10) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ EscapeFactorSigns.directedCore (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x)
      (CorrelatedEscape.payment (1/h) x) := by
  let U : ℝ := (x-(653/2000 : ℝ))/(19347/2000 : ℝ)
  have hU : U ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith only [hx.1]) (by norm_num)
    · apply (div_le_one (by norm_num : (0 : ℝ) < 19347/2000)).mpr
      linarith only [hx.2]
  have hv : ∀ i, (![46*h,U,a,b] : Fin 4 → ℝ) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · change 46*h ∈ Icc (0 : ℝ) 1
      constructor <;> nlinarith only [hh.1,hh.2]
    · exact hU
    · exact ha
    · exact hb
  have hp := EscapeReducedDirected.unit_box_nonneg _ hv
  have he : (653/2000 : ℝ)+(19347/2000 : ℝ)*U=x := by dsimp [U]; ring
  have hx0 : 0 < x := by linarith only [hx.1]
  have hH : 46*h ≠ 0 := mul_ne_zero (by norm_num : (46 : ℝ) ≠ 0) hh.1.ne'
  have hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0 := by rw [he]; exact hx0.ne'
  rw [EscapeReducedDirectedIdentity.data_identity (46*h) U a b hH hX] at hp
  have heh : (46*h)/46=h := by ring
  rw [heh,he] at hp
  have hform : 0 ≤ EscapeReducedDirectedIdentity.form h x a b :=
    nonneg_of_mul_nonneg_right hp (by norm_num)
  unfold EscapeReducedDirectedIdentity.form at hform
  have hh0 : 0 < h := hh.1
  exact nonneg_of_mul_nonneg_right hform (by positivity)

theorem reserveInner_nonneg (h x a b : ℝ) (hh : h ∈ Ioc (0 : ℝ) (1/46))
    (hx : x ∈ Icc (653/2000 : ℝ) 10) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ EscapeFactorSigns.reserveInner (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x)
      (CorrelatedEscape.payment (1/h) x) := by
  let U : ℝ := (x-(653/2000 : ℝ))/(19347/2000 : ℝ)
  have hU : U ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith only [hx.1]) (by norm_num)
    · apply (div_le_one (by norm_num : (0 : ℝ) < 19347/2000)).mpr
      linarith only [hx.2]
  have hv : ∀ i, (![46*h,U,a,b] : Fin 4 → ℝ) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · change 46*h ∈ Icc (0 : ℝ) 1
      constructor <;> nlinarith only [hh.1,hh.2]
    · exact hU
    · exact ha
    · exact hb
  have hp := EscapeReducedReserve.unit_box_nonneg _ hv
  have he : (653/2000 : ℝ)+(19347/2000 : ℝ)*U=x := by dsimp [U]; ring
  have hx0 : 0 < x := by linarith only [hx.1]
  have hH : 46*h ≠ 0 := mul_ne_zero (by norm_num : (46 : ℝ) ≠ 0) hh.1.ne'
  have hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0 := by rw [he]; exact hx0.ne'
  rw [EscapeReducedReserveIdentity.data_identity (46*h) U a b hH hX] at hp
  have heh : (46*h)/46=h := by ring
  rw [heh,he] at hp
  have hform : 0 ≤ EscapeReducedReserveIdentity.form h x a b :=
    nonneg_of_mul_nonneg_right hp (by norm_num)
  unfold EscapeReducedReserveIdentity.form at hform
  have hh0 : 0 < h := hh.1
  exact nonneg_of_mul_nonneg_right hform (by positivity)

#print axioms directedCore_nonneg
#print axioms reserveInner_nonneg
end
end Gebendorfer.RadenkovicGutman.ReducedEscapeForms
