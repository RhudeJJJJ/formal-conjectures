/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell
import Proofs.RadenkovicGutmanActualMeanOrigin
import Proofs.RadenkovicGutmanRationalIntegralPartition

namespace Gebendorfer.RadenkovicGutman.ComputedIntegralAssembly
open Set MeasureTheory CoreQuotient
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def slice (w : ComputedPolynomialCell.Witness) : RationalIntegralPartition.Slice :=
  ⟨w.a,w.b,w.total⟩
def slices (ws : List ComputedPolynomialCell.Witness) : List RationalIntegralPartition.Slice :=
  ws.map slice
def originPayment (n : ℕ) (epsilon logEpsilon logReciprocalB : ℚ) : ℚ :=
  n*epsilon*(2*logEpsilon+2*logReciprocalB-1)

noncomputable section

theorem finite_integral (x : ℚ) (p q : ℕ) (a b : ℚ)
    (ws : List ComputedPolynomialCell.Witness)
    (ha : 0≤a) (hc : RationalIntegralPartition.check a b (slices ws)=true)
    (hw : ∀ w ∈ ws, ComputedPolynomialCell.checks (ComputedGeneralPathData.build x p q) w=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (RationalIntegralPartition.total (slices ws) : ℝ)≤∫ y : ℝ in (a : ℝ)..(b : ℝ),
      MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y := by
  apply RationalIntegralPartition.integral_lower _
    (ActualFusionIntegral.logarithm_integrable G u p q (x : ℝ)) a b (slices ws) ha hc
  intro z hz
  obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hz
  exact ComputedPolynomialCell.computed_actual_integral x p q w (hw w hm) G u hd

theorem finite_integral_swapped (x : ℚ) (p q : ℕ) (a b : ℚ)
    (ws : List ComputedPolynomialCell.Witness)
    (ha : 0≤a) (hc : RationalIntegralPartition.check a b (slices ws)=true)
    (hw : ∀ w ∈ ws, ComputedPolynomialCell.checks (ComputedGeneralPathData.build x p q) w=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (RationalIntegralPartition.total (slices ws) : ℝ)≤∫ y : ℝ in (a : ℝ)..(b : ℝ),
      MixedGraphIntegral.logarithm (source G u q p) (fused G u q p) x y := by
  apply RationalIntegralPartition.integral_lower _
    (ActualFusionIntegral.logarithm_integrable G u q p (x : ℝ)) a b (slices ws) ha hc
  intro z hz
  obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hz
  exact ComputedPolynomialCell.computed_actual_integral_swapped x p q w (hw w hm) G u hd

theorem origin_integral (x epsilon logEpsilon logReciprocalB : ℚ) (p q n kE kB terms : ℕ)
    (hx : x∈Icc (0 : ℚ) 2) (he : 0<epsilon) (he1 : epsilon≤1)
    (hcE : RationalLog.accepts epsilon logEpsilon kE terms=true)
    (hcB : RationalLog.accepts (1/((n : ℚ)^2+3)) logReciprocalB kB terms=true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hN : Fintype.card V+p+q+2≤n) :
    (originPayment n epsilon logEpsilon logReciprocalB : ℝ)≤
      ∫ y : ℝ in (0 : ℝ)..(epsilon : ℝ),
        MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y := by
  have hE := RationalLog.sound epsilon logEpsilon kE terms hcE
  have hB := RationalLog.sound (1/((n : ℚ)^2+3)) logReciprocalB kB terms hcB
  push_cast at hB
  rw [one_div,Real.log_inv] at hB
  have hlog : 2*(logEpsilon : ℝ)+2*(logReciprocalB : ℝ)-1≤
      Real.log (epsilon : ℝ)-Real.log ((n : ℝ)^2+3)-1 := by linarith only [hE,hB]
  have her : (0 : ℝ)<epsilon := by exact_mod_cast he
  have hp := mul_le_mul_of_nonneg_left hlog
    (show 0≤(n : ℝ)*(epsilon : ℝ) from mul_nonneg (Nat.cast_nonneg n) her.le)
  have hpr : (originPayment n epsilon logEpsilon logReciprocalB : ℝ)≤
      (n : ℝ)*(epsilon : ℝ)*(Real.log (epsilon : ℝ)-Real.log ((n : ℝ)^2+3)-1) := by
    simpa only [originPayment,Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat,
      Rat.cast_natCast] using hp
  exact hpr.trans (ActualMeanOrigin.actual_origin_lower G u p q n hN x epsilon
    ⟨by exact_mod_cast hx.1,by exact_mod_cast hx.2⟩ her (by exact_mod_cast he1))

theorem normalized_lower (x a Y target O B T : ℚ) (p q : ℕ)
    (ha : 0≤a) (haY : a≤Y) (ht : 0≤target)
    (hbudget : target*(3927/1250)≤O+B+T)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (u : V)
    (ho : (O : ℝ)≤∫ y : ℝ in (0 : ℝ)..(a : ℝ),
      MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y)
    (hb : (B : ℝ)≤∫ y : ℝ in (a : ℝ)..(Y : ℝ),
      MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y)
    (hT : (T : ℝ)≤∫ y : ℝ in Ioi (Y : ℝ),
      MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) x y) :
    (target : ℝ)≤ActualFusionIntegral.normalizedIntegral G u p q x := by
  let f := MixedGraphIntegral.logarithm (source G u p q) (fused G u p q) (x : ℝ)
  have hall := RationalIntegralPartition.three_region_lower f
    (ActualFusionIntegral.logarithm_integrable G u p q x) a Y O B T
    (by exact_mod_cast ha) (by exact_mod_cast haY) ho hb hT
  have hpi : Real.pi≤(3927/1250 : ℝ) := le_trans Real.pi_lt_d4.le (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hpi (show (0 : ℝ)≤target by exact_mod_cast ht)
  have hbr : (target : ℝ)*(3927/1250)≤(O : ℝ)+(B : ℝ)+(T : ℝ) := by exact_mod_cast hbudget
  have hi := hm.trans (hbr.trans hall)
  have hdiv := (le_div_iff₀ Real.pi_pos).mpr hi
  change (target : ℝ)≤(1/Real.pi)*(∫ y : ℝ in Ioi 0, f y)
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hdiv

#print axioms finite_integral
#print axioms finite_integral_swapped
#print axioms origin_integral
#print axioms normalized_lower
end
end Gebendorfer.RadenkovicGutman.ComputedIntegralAssembly
