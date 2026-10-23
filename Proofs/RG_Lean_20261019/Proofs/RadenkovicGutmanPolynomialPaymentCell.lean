/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathPolynomialPayments
import Proofs.RadenkovicGutmanRationalPolynomialOrder
import Proofs.RadenkovicGutmanRationalPolynomialAffineIntegral

namespace Gebendorfer.RadenkovicGutman.PolynomialPaymentCell
open Polynomial PolynomialPathMap RationalComplexPolynomial RationalPolynomialCell
open Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

structure Cell where
  a : ℚ
  b : ℚ
  s : List ℚ
  L : List ℚ
  pay : List ℚ
  primitive : List ℚ
  c : ℚ
  R : ℚ
  unitIntegral : ℚ
  total : ℚ
  k : ℕ
  n : ℕ
  comparisonDegree : ℕ
  nDegree : ℕ
  eDegree : ℕ
  sCoefficients : Fin 3 → ℚ
  lowerCoefficients : Fin 5 → ℚ
  comparisonCoefficients : Fin (comparisonDegree+1) → ℚ
  nCoefficients : Fin (nDegree+1) → ℚ
  eCoefficients : Fin (eDegree+1) → ℚ

def comparison (us vs js : List ℚ) (z : Cell) : ℚ[X] :=
  let S := ofList z.s
  let A := affine z.a z.b
  S*(ofList js).comp A - ofList z.L*
    ((S+S^2)*(ofList us).comp A+(S+1)*(ofList vs).comp A)

def accepts (us vs js ns es : List ℚ) (z : Cell) : Bool :=
  decide (0 < z.a ∧ z.a < z.b ∧ 0 < z.c ∧
    ofList z.s = form 2 z.sCoefficients ∧ (∀ i, 0 < z.sCoefficients i) ∧
    ofList z.L-C z.c = form 4 z.lowerCoefficients ∧ (∀ i, 0 ≤ z.lowerCoefficients i) ∧
    comparison us vs js z = form z.comparisonDegree z.comparisonCoefficients ∧
      (∀ i, 0 ≤ z.comparisonCoefficients i) ∧
    (ofList ns).comp (affine z.a z.b) = form z.nDegree z.nCoefficients ∧
      (∀ i, 0 < z.nCoefficients i) ∧
    (ofList es).comp (affine z.a z.b) = form z.eDegree z.eCoefficients ∧
      (∀ i, 0 < z.eCoefficients i))

def paymentAccepts (z : Cell) : Bool :=
  decide (ofList z.pay = GeneralPathPolynomialPayments.paymentPolynomial (ofList z.L) z.c z.R ∧
    z.total ≤ (z.b-z.a)*z.unitIntegral)

def ordinate (z : Cell) (y : ℝ) : ℝ := (y-(z.a : ℝ))/((z.b : ℝ)-z.a)
def density (z : Cell) (y : ℝ) : ℝ := realEvaluator (ordinate z y) (ofList z.pay)

theorem pointwise (x : ℚ) (p q : ℕ) (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es = true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep = true)
    (z : Cell) (hz : accepts us vs js ns sep z = true)
    (hpay : paymentAccepts z = true) (hl : RationalLog.accepts z.c z.R z.k z.n = true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1)
    (y : ℝ) (hy : y ∈ Icc (z.a : ℝ) (z.b : ℝ)) :
    density z y ≤ MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
      (CoreQuotient.fused G u p q) x y := by
  obtain ⟨ha,hab,hc,hs,hsp,hL,hLp,hP,hPp,hn,hnp,he,hep⟩ := of_decide_eq_true hz
  obtain ⟨hpayment,_⟩ := of_decide_eq_true hpay
  let t := ordinate z y
  have ht : t ∈ Icc (0 : ℝ) 1 := cell_coordinate z.a z.b hab y hy
  have hs0 := RationalPolynomialOrder.form_positive _ 2 z.sCoefficients hs hsp t ht
  have hL0 := RationalPolynomialOrder.form_nonneg _ 4 z.lowerCoefficients hL hLp t ht
  rw [map_sub,real_C] at hL0
  have hN := RationalPolynomialOrder.form_positive _ z.nDegree z.nCoefficients hn hnp t ht
  have hE := RationalPolynomialOrder.form_positive _ z.eDegree z.eCoefficients he hep t ht
  have hPr := RationalPolynomialOrder.form_nonneg _ z.comparisonDegree
    z.comparisonCoefficients hP hPp t ht
  have habr : (z.a : ℝ) < z.b := by exact_mod_cast hab
  have hcoord : (z.a : ℝ)+((z.b : ℝ)-z.a)*t = y := by
    dsimp [t,ordinate]
    field_simp [ne_of_gt (sub_pos.mpr habr)]
    <;> ring
  rw [affine_evaluation,hcoord] at hN hE
  simp only [comparison,map_sub,map_mul,map_add,map_pow,map_one,affine_evaluation,hcoord] at hPr
  have hy0 : 0 < y := lt_of_lt_of_le (by exact_mod_cast ha) hy.1
  have h := GeneralPathPolynomialPayments.actual_log_lower x y hy0 p q
    as bs cs es us vs js ns sep hpath hpoly (realEvaluator t (ofList z.s))
    (realEvaluator t (ofList z.L)) hs0 hN hE (sub_nonneg.mp hPr) z.c z.R z.k z.n
    hc (sub_nonneg.mp hL0) hl G u hd
  rw [density,hpayment,GeneralPathPolynomialPayments.payment_evaluation]
  exact h

theorem integral (z : Cell) (hz : z.a < z.b)
    (hi : RationalPolynomialIntegral.accepts z.pay z.primitive 0 1 z.unitIntegral = true)
    (hp : paymentAccepts z = true) :
    (z.total : ℝ) ≤ ∫ y : ℝ in (z.a : ℝ)..(z.b : ℝ), density z y := by
  have h := RationalPolynomialAffineIntegral.sound z.pay z.primitive z.a z.b z.unitIntegral hz hi
  change (z.total : ℝ) ≤ ∫ y : ℝ in (z.a : ℝ)..(z.b : ℝ),
    realEvaluator ((y-(z.a : ℝ))/((z.b : ℝ)-z.a)) (ofList z.pay)
  rw [h]
  exact_mod_cast (of_decide_eq_true hp).2

theorem density_continuous (z : Cell) : Continuous (density z) :=
  (RationalPolynomialIntegral.evaluation_continuous (ofList z.pay)).comp
    ((continuous_id.sub continuous_const).div_const _)

theorem actual_integral_lower (x : ℚ) (p q : ℕ) (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es = true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep = true)
    (z : Cell) (hz : accepts us vs js ns sep z = true)
    (hpay : paymentAccepts z = true) (hl : RationalLog.accepts z.c z.R z.k z.n = true)
    (hi : RationalPolynomialIntegral.accepts z.pay z.primitive 0 1 z.unitIntegral = true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1)
    (hf : IntervalIntegrable (MixedGraphIntegral.logarithm
      (CoreQuotient.source G u p q) (CoreQuotient.fused G u p q) x) volume (z.a : ℝ) (z.b : ℝ)) :
    (z.total : ℝ) ≤ ∫ y : ℝ in (z.a : ℝ)..(z.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
        (CoreQuotient.fused G u p q) x y := by
  have hab := (of_decide_eq_true hz).2.1
  have habr : (z.a : ℝ) ≤ z.b := by exact_mod_cast hab.le
  exact le_trans (integral z hab hi hpay)
    (intervalIntegral.integral_mono_on habr ((density_continuous z).intervalIntegrable _ _) hf
      (fun y hy => pointwise x p q as bs cs es us vs js ns sep hpath hpoly z hz hpay hl G u hd y hy))

#print axioms pointwise
#print axioms integral
#print axioms density_continuous
#print axioms actual_integral_lower
end
end Gebendorfer.RadenkovicGutman.PolynomialPaymentCell
