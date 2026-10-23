/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedGeneralPathData
import Proofs.RadenkovicGutmanInversePolynomialNorm
import Proofs.RadenkovicGutmanRationalPolynomialOrder
import Proofs.RadenkovicGutmanQuantitativePositiveTail

namespace Gebendorfer.RadenkovicGutman.ComputedPositiveTail
open Polynomial PolynomialPathMap RationalComplexPolynomial CoreQuotient
open Set MeasureTheory
open scoped Classical
abbrev Poly := HornerCertificates.Poly
abbrev Data := ComputedGeneralPathData.Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def multiplier : Poly := [0,0,0,2]
def denominator (d : Data) : Poly :=
  ComputedHornerArithmetic.plus
    (ComputedHornerArithmetic.times (ComputedHornerArithmetic.plus multiplier [1]) d.U)
    (ComputedHornerArithmetic.times
      (ComputedHornerArithmetic.plus (ComputedHornerArithmetic.square multiplier) multiplier) d.V)
def comparison (d : Data) (K : ℚ) : Poly :=
  ComputedHornerArithmetic.difference
    (ComputedHornerArithmetic.times [0,0,1]
      (ComputedHornerArithmetic.difference (ComputedHornerArithmetic.times multiplier d.J) (denominator d)))
    (ComputedHornerArithmetic.scaled K (denominator d))
def shifted (p : Poly) (Y : ℚ) : Poly := ComputedHornerArithmetic.affine p Y 1
def checks (d : Data) (K Y : ℚ) : Bool :=
  decide (0≤K ∧ 0<Y ∧
    ComputedHornerArithmetic.nonnegative (shifted (comparison d K) Y)=true ∧
    ComputedHornerArithmetic.nonnegative (shifted d.N Y)=true ∧
    ComputedHornerArithmetic.nonnegative (shifted d.E Y)=true ∧
    0<(shifted d.N Y).headD 0 ∧ 0<(shifted d.E Y).headD 0)

noncomputable section

theorem shifted_checked (p : Poly) (Y : ℚ)
    (hc : ComputedHornerArithmetic.nonnegative (shifted p Y)=true) :
    RationalPolynomialOrder.rayAccepts (ofList p) Y (shifted p Y)=true := by
  rw [RationalPolynomialOrder.rayAccepts,decide_eq_true_eq]
  have he : RationalPolynomialCell.affine Y (Y+1)=ofList [Y,1] := by
    simp [RationalPolynomialCell.affine,ofList]
  refine ⟨?_,?_⟩
  · simpa only [shifted,ComputedHornerArithmetic.affine,he] using
      (ComputedHornerArithmetic.ofList_compose p [Y,1]).symm
  · simpa only [ComputedHornerArithmetic.nonnegative,List.all_eq_true,decide_eq_true_eq] using hc

theorem comparison_sound (d : Data) (K : ℚ) :
    ofList (comparison d K)=
      X^2*((C 2*X^3)*ofList d.J-
        (((C 2*X^3)+1)*ofList d.U+((C 2*X^3)^2+(C 2*X^3))*ofList d.V))-
      C K*(((C 2*X^3)+1)*ofList d.U+((C 2*X^3)^2+(C 2*X^3))*ofList d.V) := by
  simp only [comparison,denominator,multiplier,ComputedHornerArithmetic.ofList_difference,
    ComputedHornerArithmetic.ofList_plus,ComputedHornerArithmetic.ofList_times,
    ComputedHornerArithmetic.ofList_scaled,ComputedHornerArithmetic.ofList_square,
    ofList,map_zero,map_one,mul_zero,add_zero,zero_add]
  ring

theorem actual_squared_norm (x : ℚ) (p q : ℕ) (d : Data)
    (hpath : GeneralPathPolynomials.accepts x p q d.a d.b d.c d.e=true)
    (hpoly : RationalMobiusPolynomials.accepts d.a d.b d.c d.e d.U d.V d.J d.N d.E=true)
    (K Y : ℚ) (hc : checks d K Y=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) (y : ℝ) (hy : (Y : ℝ)≤y) :
    1+(K : ℝ)/y^2≤
      ‖(CoreQuotient.shifted (point x y) (source G u p q)).det /
        (CoreQuotient.shifted (point x y) (fused G u p q)).det‖^2 := by
  obtain ⟨_hK,hY,hP,hN,hE,hN0,hE0⟩ := of_decide_eq_true hc
  have hYr : (0 : ℝ)<Y := by exact_mod_cast hY
  have hy0 : 0<y := hYr.trans_le hy
  have hnp := RationalPolynomialOrder.ray_positive (ofList d.N) Y (shifted d.N Y)
    (shifted_checked d.N Y hN) hN0 y hy
  have hep := RationalPolynomialOrder.ray_positive (ofList d.E) Y (shifted d.E Y)
    (shifted_checked d.E Y hE) hE0 y hy
  have hpc := RationalPolynomialOrder.ray_nonneg (ofList (comparison d K)) Y
    (shifted (comparison d K) Y) (shifted_checked _ Y hP) y hy
  rw [comparison_sound] at hpc
  simp only [map_sub,map_mul,map_add,map_pow,map_one,real_C,real_X] at hpc
  have hb := InversePolynomialNorm.reserve_bound _ _ _ (K : ℝ) y hy0 hpc
  have hi := InversePolynomialNorm.inverse_parameter _ _ _ (2*y^3)
    (1+(K : ℝ)/y^2) (by positivity) hb
  exact GeneralPathPolynomialPayments.actual_norm_lower x y hy0 p q
    d.a d.b d.c d.e d.U d.V d.J d.N d.E hpath hpoly
    (1/(2*y^3)) (1+(K : ℝ)/y^2) (by positivity) hnp hep hi G u hd

theorem actual_integral (x : ℚ) (p q : ℕ) (d : Data)
    (hpath : GeneralPathPolynomials.accepts x p q d.a d.b d.c d.e=true)
    (hpoly : RationalMobiusPolynomials.accepts d.a d.b d.c d.e d.U d.V d.J d.N d.E=true)
    (K Y : ℚ) (hc : checks d K Y=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ)≤
      ∫ y : ℝ in Ioi (Y : ℝ),
        MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y := by
  have hh := of_decide_eq_true hc
  have hK : (0 : ℝ)≤K := by exact_mod_cast hh.1
  have hY : (0 : ℝ)<Y := by exact_mod_cast hh.2.1
  have hf := (ActualFusionIntegral.logarithm_integrable G u p q (x : ℝ)).mono_set
    (show Ioi (Y : ℝ)⊆Ioi 0 from fun _ hy => hY.trans hy)
  apply QuantitativePositiveTail.integral_lower _ (K : ℝ) (Y : ℝ) hK hY hf
  intro y hy
  exact QuantitativePositiveTail.pointwise (K : ℝ) (Y : ℝ) y _ hK hY hy.le
    (actual_squared_norm x p q d hpath hpoly K Y hc G u hd y hy.le)

theorem computed_actual_integral (x : ℚ) (p q : ℕ) (K Y : ℚ)
    (hc : checks (ComputedGeneralPathData.build x p q) K Y=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ)≤
      ∫ y : ℝ in Ioi (Y : ℝ),
        MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y :=
  actual_integral x p q _ (ComputedGeneralPathData.path_checked x p q)
    (ComputedGeneralPathData.norms_checked x p q) K Y hc G u hd

theorem computed_actual_integral_swapped (x : ℚ) (p q : ℕ) (K Y : ℚ)
    (hc : checks (ComputedGeneralPathData.build x p q) K Y=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    QuantitativePositiveTail.coefficient (K : ℝ) (Y : ℝ)/(Y : ℝ)≤
      ∫ y : ℝ in Ioi (Y : ℝ),
        MixedGraphIntegral.logarithm (source G u q p) (fused G u q p) x y :=
  actual_integral x q p _ (ComputedGeneralPathData.path_swapped x p q)
    (ComputedGeneralPathData.norms_checked x p q) K Y hc G u hd

#print axioms shifted_checked
#print axioms comparison_sound
#print axioms actual_squared_norm
#print axioms actual_integral
#print axioms computed_actual_integral
#print axioms computed_actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.ComputedPositiveTail
