/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPolynomialPaymentCell
import Proofs.RadenkovicGutmanHornerArithmetic

namespace Gebendorfer.RadenkovicGutman.FastPolynomialPaymentCell
open PolynomialPaymentCell PolynomialPathMap RationalComplexPolynomial HornerCertificates
open Set MeasureTheory
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

structure Geometry where
  U : List ℚ
  V : List ℚ
  J : List ℚ
  N : List ℚ
  E : List ℚ
  sFloor : ℚ
  nFloor : ℚ
  eFloor : ℚ
  sourceDegree : ℕ

/-- Complete exact interpolation and proved degree bounds establish the affine
identities; coefficient checks then cover every real point of the cell. -/
def accepts (us vs js ns es : List ℚ) (z : Cell) (g : Geometry) : Bool :=
  decide (0 < z.a ∧ z.a < z.b ∧ 0 < z.c ∧
    0 < g.sFloor ∧ 0 < g.nFloor ∧ 0 < g.eFloor ∧
    affineCheck g.sourceDegree us g.U z.a (z.b-z.a) = true ∧
    affineCheck g.sourceDegree vs g.V z.a (z.b-z.a) = true ∧
    affineCheck g.sourceDegree js g.J z.a (z.b-z.a) = true ∧
    affineCheck g.sourceDegree ns g.N z.a (z.b-z.a) = true ∧
    affineCheck g.sourceDegree es g.E z.a (z.b-z.a) = true ∧
    HornerCertificates.accepts 2 (HornerArithmetic.floorMargin z.s g.sFloor) = true ∧
    HornerCertificates.accepts 4 (HornerArithmetic.floorMargin z.L z.c) = true ∧
    HornerCertificates.accepts z.nDegree (HornerArithmetic.floorMargin g.N g.nFloor) = true ∧
    HornerCertificates.accepts z.eDegree (HornerArithmetic.floorMargin g.E g.eFloor) = true ∧
    HornerCertificates.accepts z.comparisonDegree (HornerArithmetic.normMargin z.s z.L g.U g.V g.J) = true)

open scoped Classical
noncomputable section

theorem pointwise (x : ℚ) (p q : ℕ) (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es = true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep = true)
    (z : Cell) (g : Geometry) (hg : accepts us vs js ns sep z g = true)
    (hpay : paymentAccepts z = true) (hl : RationalLog.accepts z.c z.R z.k z.n = true)
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (u : W) (hd : G.degree u = 1)
    (y : ℝ) (hy : y ∈ Icc (z.a : ℝ) (z.b : ℝ)) :
    density z y ≤ MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
      (CoreQuotient.fused G u p q) x y := by
  obtain ⟨ha,hab,hc,hsF,hnF,heF,hu,hv,hj,hn,he,hs0,hl0,hn0,he0,hp0⟩ := of_decide_eq_true hg
  obtain ⟨hpayment,_⟩ := of_decide_eq_true hpay
  let t := ordinate z y
  have ht : t ∈ Icc (0 : ℝ) 1 := RationalPolynomialCell.cell_coordinate z.a z.b hab y hy
  have habr : (z.a : ℝ) < z.b := by exact_mod_cast hab
  have hcoord : (z.a : ℝ)+((z.b : ℝ)-z.a)*t = y := by
    dsimp [t,ordinate]
    field_simp [ne_of_gt (sub_pos.mpr habr)]
    ring
  have hU := affineCheck_sound g.sourceDegree us g.U z.a (z.b-z.a) hu t
  have hV := affineCheck_sound g.sourceDegree vs g.V z.a (z.b-z.a) hv t
  have hJ := affineCheck_sound g.sourceDegree js g.J z.a (z.b-z.a) hj t
  have hN := affineCheck_sound g.sourceDegree ns g.N z.a (z.b-z.a) hn t
  have hE := affineCheck_sound g.sourceDegree sep g.E z.a (z.b-z.a) he t
  simp only [Rat.cast_sub,hcoord] at hU hV hJ hN hE
  rw [HornerArithmetic.real_evaluation us y] at hU
  rw [HornerArithmetic.real_evaluation vs y] at hV
  rw [HornerArithmetic.real_evaluation js y] at hJ
  rw [HornerArithmetic.real_evaluation ns y] at hN
  rw [HornerArithmetic.real_evaluation sep y] at hE
  have hS := accepts_sound 2 _ hs0 t ht
  have hL := accepts_sound 4 _ hl0 t ht
  have hNs := accepts_sound z.nDegree _ hn0 t ht
  have hEs := accepts_sound z.eDegree _ he0 t ht
  rw [HornerArithmetic.evaluate_floorMargin] at hS hL hNs hEs
  rw [hN] at hNs
  rw [hE] at hEs
  have hs : 0 < evaluate z.s t := by
    have hsf : (0 : ℝ) < g.sFloor := by exact_mod_cast hsF
    linarith
  have hnPos : 0 < realEvaluator y (ofList ns) := by
    have hnf : (0 : ℝ) < g.nFloor := by exact_mod_cast hnF
    linarith
  have hePos : 0 < realEvaluator y (ofList sep) := by
    have hef : (0 : ℝ) < g.eFloor := by exact_mod_cast heF
    linarith
  have hP := accepts_sound z.comparisonDegree _ hp0 t ht
  rw [HornerArithmetic.evaluate_normMargin,hU,hV,hJ] at hP
  have hy0 : 0 < y := lt_of_lt_of_le (by exact_mod_cast ha) hy.1
  have h := GeneralPathPolynomialPayments.actual_log_lower x y hy0 p q as bs cs es us vs js ns sep
    hpath hpoly (evaluate z.s t) (evaluate z.L t) hs hnPos hePos (sub_nonneg.mp hP)
    z.c z.R z.k z.n hc (sub_nonneg.mp hL) hl G u hd
  change realEvaluator t (ofList z.pay) ≤ _
  rw [hpayment,GeneralPathPolynomialPayments.payment_evaluation,
    ← HornerArithmetic.real_evaluation z.L t]
  exact h

theorem actual_integral_lower (x : ℚ) (p q : ℕ) (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es = true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep = true)
    (z : Cell) (g : Geometry) (hg : accepts us vs js ns sep z g = true)
    (hpay : paymentAccepts z = true) (hl : RationalLog.accepts z.c z.R z.k z.n = true)
    (hi : RationalPolynomialIntegral.accepts z.pay z.primitive 0 1 z.unitIntegral = true)
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (u : W) (hd : G.degree u = 1)
    (hf : IntervalIntegrable (MixedGraphIntegral.logarithm
      (CoreQuotient.source G u p q) (CoreQuotient.fused G u p q) x) volume (z.a : ℝ) (z.b : ℝ)) :
    (z.total : ℝ) ≤ ∫ y : ℝ in (z.a : ℝ)..(z.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
        (CoreQuotient.fused G u p q) x y := by
  have hab := (of_decide_eq_true hg).2.1
  have habr : (z.a : ℝ) ≤ z.b := by exact_mod_cast hab.le
  exact le_trans (PolynomialPaymentCell.integral z hab hi hpay)
    (intervalIntegral.integral_mono_on habr ((density_continuous z).intervalIntegrable _ _) hf
      (fun y hy => pointwise x p q as bs cs es us vs js ns sep hpath hpoly z g hg hpay hl G u hd y hy))

#print axioms pointwise
#print axioms actual_integral_lower
end
end Gebendorfer.RadenkovicGutman.FastPolynomialPaymentCell
