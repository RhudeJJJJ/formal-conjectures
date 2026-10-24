/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.SemanticPolynomialPaymentCell
open Set MeasureTheory PolynomialPathMap RationalComplexPolynomial
open PolynomialPaymentCell HornerCertificates
abbrev Witness := ComputedPolynomialCell.Witness
abbrev Data := ComputedGeneralPathData.Data
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def cell (w : Witness) : PolynomialPaymentCell.Cell :=
  let pay := ComputedHornerArithmetic.paymentList w.L w.c w.R
  {a:=w.a,b:=w.b,s:=w.s,L:=w.L,pay:=pay,
   primitive:=ComputedHornerArithmetic.primitive pay,c:=w.c,R:=w.R,
   unitIntegral:=ComputedHornerArithmetic.unitIntegral pay,total:=w.total,k:=w.k,n:=w.n,
   comparisonDegree:=0,nDegree:=0,eDegree:=0,
   sCoefficients:=fun _ => 0,lowerCoefficients:=fun _ => 0,
   comparisonCoefficients:=fun _ => 0,nCoefficients:=fun _ => 0,eCoefficients:=fun _ => 0}

def Budget (w : Witness) : Prop :=
  w.total≤(w.b-w.a)*ComputedHornerArithmetic.unitIntegral
    (ComputedHornerArithmetic.paymentList w.L w.c w.R)

theorem payment_checked (w : Witness) (h : Budget w) : paymentAccepts (cell w)=true := by
  rw [paymentAccepts,decide_eq_true_eq]
  exact ⟨ComputedHornerArithmetic.paymentList_sound w.L w.c w.R,h⟩

theorem primitive_checked (w : Witness) :
    RationalPolynomialIntegral.accepts (cell w).pay (cell w).primitive 0 1 (cell w).unitIntegral=true :=
  ComputedHornerArithmetic.primitive_checked (ComputedHornerArithmetic.paymentList w.L w.c w.R)

noncomputable section
def location (w : Witness) (t : ℝ) : ℝ :=
  (w.a : ℝ)+((w.b-w.a : ℚ) : ℝ)*t

/-- These pointwise conditions retain every positivity and comparison obligation
of the original polynomial cell, independently of the arithmetic representation. -/
def Conditions (d : Data) (w : Witness) : Prop :=
  0<w.a ∧ w.a<w.b ∧ 0<w.c ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    0<evaluate w.s t ∧ (w.c : ℝ)≤evaluate w.L t ∧
    0<evaluate d.N (location w t) ∧ 0<evaluate d.E (location w t) ∧
    evaluate w.L t*((evaluate w.s t+(evaluate w.s t)^2)*evaluate d.U (location w t)+
      (evaluate w.s t+1)*evaluate d.V (location w t))≤
      evaluate w.s t*evaluate d.J (location w t)

theorem pointwise (x : ℚ) (p q : ℕ) (d : Data)
    (hpath : GeneralPathPolynomials.accepts x p q d.a d.b d.c d.e=true)
    (hpoly : RationalMobiusPolynomials.accepts d.a d.b d.c d.e d.U d.V d.J d.N d.E=true)
    (w : Witness) (hcnd : Conditions d w) (hb : Budget w)
    (hl : RationalLog.accepts w.c w.R w.k w.n=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1)
    (y : ℝ) (hy : y ∈ Icc (w.a : ℝ) (w.b : ℝ)) :
    density (cell w) y≤MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
      (CoreQuotient.fused G u p q) x y := by
  obtain ⟨ha,hab,hc,hconditions⟩ := hcnd
  let t := ordinate (cell w) y
  have ht : t ∈ Icc (0 : ℝ) 1 := RationalPolynomialCell.cell_coordinate w.a w.b hab y hy
  have habr : (w.a : ℝ)<w.b := by exact_mod_cast hab
  have hcoord : (w.a : ℝ)+((w.b : ℝ)-w.a)*t=y := by
    dsimp [t,ordinate,cell]
    field_simp [ne_of_gt (sub_pos.mpr habr)]
    ring
  have hloc : location w t=y := by simpa only [location,Rat.cast_sub] using hcoord
  obtain ⟨hs,hL,hN,hE,hP⟩ := hconditions t ht
  have hnPos : 0<realEvaluator y (ofList d.N) := by
    rw [← HornerArithmetic.real_evaluation]
    simpa only [hloc] using hN
  have hePos : 0<realEvaluator y (ofList d.E) := by
    rw [← HornerArithmetic.real_evaluation]
    simpa only [hloc] using hE
  have hP' : evaluate w.L t*((evaluate w.s t+(evaluate w.s t)^2)*realEvaluator y (ofList d.U)+
      (evaluate w.s t+1)*realEvaluator y (ofList d.V))≤
      evaluate w.s t*realEvaluator y (ofList d.J) := by
    simpa only [hloc,HornerArithmetic.real_evaluation] using hP
  have hy0 : 0<y := lt_of_lt_of_le (by exact_mod_cast ha) hy.1
  have h := GeneralPathPolynomialPayments.actual_log_lower x y hy0 p q
    d.a d.b d.c d.e d.U d.V d.J d.N d.E hpath hpoly
    (evaluate w.s t) (evaluate w.L t) hs hnPos hePos hP'
    w.c w.R w.k w.n hc hL hl G u hd
  obtain ⟨hpayment,_⟩ := of_decide_eq_true (payment_checked w hb)
  change realEvaluator t (ofList (cell w).pay)≤_
  rw [hpayment,GeneralPathPolynomialPayments.payment_evaluation,
    ← HornerArithmetic.real_evaluation w.L t]
  exact h

theorem actual_integral_lower (x : ℚ) (p q : ℕ) (d : Data)
    (hpath : GeneralPathPolynomials.accepts x p q d.a d.b d.c d.e=true)
    (hpoly : RationalMobiusPolynomials.accepts d.a d.b d.c d.e d.U d.V d.J d.N d.E=true)
    (w : Witness) (hcnd : Conditions d w) (hb : Budget w)
    (hl : RationalLog.accepts w.c w.R w.k w.n=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (w.total : ℝ)≤∫ y : ℝ in (w.a : ℝ)..(w.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u p q)
        (CoreQuotient.fused G u p q) x y := by
  have ha : (0 : ℝ)≤w.a := by exact_mod_cast hcnd.1.le
  have habr : (w.a : ℝ)≤w.b := by exact_mod_cast hcnd.2.1.le
  have hf := TailIntegral.interval_integrable_of_Ioi
    (ActualFusionIntegral.logarithm_integrable G u p q (x : ℝ)) ha habr
  exact le_trans (PolynomialPaymentCell.integral (cell w) hcnd.2.1
    (primitive_checked w) (payment_checked w hb))
    (intervalIntegral.integral_mono_on habr ((density_continuous (cell w)).intervalIntegrable _ _) hf
      (fun y hy => pointwise x p q d hpath hpoly w hcnd hb hl G u hd y hy))

#print axioms payment_checked
#print axioms primitive_checked
#print axioms pointwise
#print axioms actual_integral_lower
end
end Gebendorfer.RadenkovicGutman.SemanticPolynomialPaymentCell
