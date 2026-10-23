/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalPolynomialIntegral

namespace Gebendorfer.RadenkovicGutman.RationalPolynomialAffineIntegral
open Polynomial PolynomialPathMap RationalComplexPolynomial MeasureTheory
noncomputable section

theorem sound (p F : List ℚ) (a b L : ℚ) (hab : a < b)
    (hcheck : RationalPolynomialIntegral.accepts p F 0 1 L = true) :
    (∫ y : ℝ in (a : ℝ)..(b : ℝ),
      realEvaluator ((y-(a : ℝ))/((b : ℝ)-a)) (ofList p)) =
      ((b : ℝ)-a)*(L : ℝ) := by
  obtain ⟨hd,he⟩ := of_decide_eq_true hcheck
  have hw : (b : ℝ)-(a : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.ne')
  let w : ℝ := (b : ℝ)-a
  have hw' : w ≠ 0 := hw
  have hf (y : ℝ) : HasDerivAt
      (fun z => w*realEvaluator ((z-(a : ℝ))/w) (ofList F))
      (realEvaluator ((y-(a : ℝ))/w) (ofList p)) y := by
    have hp := RationalPolynomialIntegral.derivative_evaluation (ofList F) ((y-(a : ℝ))/w)
    rw [hd] at hp
    have h := (hp.comp y (((hasDerivAt_id y).sub_const (a : ℝ)).div_const w)).const_mul w
    convert h using 1 <;> first
      | rfl
      | field_simp [hw']
  have hc : Continuous (fun y : ℝ => realEvaluator ((y-(a : ℝ))/w) (ofList p)) :=
    (RationalPolynomialIntegral.evaluation_continuous (ofList p)).comp
      ((continuous_id.sub continuous_const).div_const w)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hf y)
    (hc.intervalIntegrable (a : ℝ) (b : ℝ))
  have h0 : ((a : ℝ)-a)/w = 0 := by simp
  have h1 : ((b : ℝ)-a)/w = 1 := div_self hw'
  rw [h0,h1,show (0 : ℝ)=((0 : ℚ) : ℝ) by norm_num,
    show (1 : ℝ)=((1 : ℚ) : ℝ) by norm_num,
    RationalPolynomialIntegral.rational_evaluation,
    RationalPolynomialIntegral.rational_evaluation] at hi
  calc
    _ = w*((((ofList F).eval 1 : ℚ) : ℝ)-(((ofList F).eval 0 : ℚ) : ℝ)) := by
      rw [hi]; ring
    _ = _ := by rw [← Rat.cast_sub,he]

#print axioms sound
end
end Gebendorfer.RadenkovicGutman.RationalPolynomialAffineIntegral
