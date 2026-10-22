/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastArmCover
import Proofs.RadenkovicGutmanFastPaidDegreeOneClass

namespace Gebendorfer.RadenkovicGutman.FastArmCoverIntegral
set_option maxHeartbeats 0

structure Slice where
  cover : FastArmCover.Cover
  lower : ℚ
  upper : ℚ
  bound : ℚ

def accepts (d : ℚ) (c₁ c₂ : Fin 5) (c : Slice) : Bool :=
  decide (0 < c.lower ∧ c.lower < c.upper ∧
    FastArmCover.accepts d c₁ c₂ c.lower c.upper 0 1 0 1 c.bound c.cover=true)

def checkAt (d : ℚ) (c₁ c₂ : Fin 5) : ℚ → ℚ → List Slice → Bool
  | a,b,[] => decide (a=b)
  | a,b,c::cs => decide (c.lower=a) && accepts d c₁ c₂ c && checkAt d c₁ c₂ c.upper b cs

def payment : List Slice → ℚ
  | [] => 0
  | c::cs => (c.upper-c.lower)*c.bound+payment cs

theorem accepts_of_checks (d : ℚ) (c₁ c₂ : Fin 5) (c : Slice)
    (ha : 0 < c.lower) (hab : c.lower < c.upper)
    (hc : FastArmCover.accepts d c₁ c₂ c.lower c.upper 0 1 0 1 c.bound c.cover=true) :
    accepts d c₁ c₂ c=true := by
  exact decide_eq_true (And.intro ha (And.intro hab hc))

theorem accepts_parts (d : ℚ) (c₁ c₂ : Fin 5) (c : Slice) (h : accepts d c₁ c₂ c=true) :
    0 < c.lower ∧ c.lower < c.upper ∧
    FastArmCover.accepts d c₁ c₂ c.lower c.upper 0 1 0 1 c.bound c.cover=true :=
  of_decide_eq_true h

theorem checked_cons (d : ℚ) (c₁ c₂ : Fin 5) (a b : ℚ) (c : Slice) (cs : List Slice)
    (hc : c.lower=a) (hpaid : accepts d c₁ c₂ c=true)
    (hrest : checkAt d c₁ c₂ c.upper b cs=true) : checkAt d c₁ c₂ a b (c::cs)=true := by
  simp only [checkAt,hc,decide_true,Bool.true_and,hpaid,hrest]

theorem cons_parts (d : ℚ) (c₁ c₂ : Fin 5) (a b : ℚ) (c : Slice) (cs : List Slice)
    (h : checkAt d c₁ c₂ a b (c::cs)=true) :
    c.lower=a ∧ accepts d c₁ c₂ c=true ∧ checkAt d c₁ c₂ c.upper b cs=true := by
  simpa only [checkAt,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h

theorem endpoints_order (d : ℚ) (c₁ c₂ : Fin 5) (a b : ℚ) (cs : List Slice)
    (h : checkAt d c₁ c₂ a b cs=true) : a ≤ b := by
  induction cs generalizing a with
  | nil => exact (of_decide_eq_true h : a=b).le
  | cons c cs ih =>
    obtain ⟨he,hc,hr⟩ := cons_parts d c₁ c₂ a b c cs h
    have hstep : c.lower < c.upper := (accepts_parts d c₁ c₂ c hc).2.1
    rw [he] at hstep
    exact hstep.le.trans (ih c.upper hr)

noncomputable section
open CoreQuotient Set MeasureTheory ActualFusionIntegral
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_lower (C : SimpleGraph V) (u : V) (p q d : ℕ) (hd : 1 ≤ d)
    (hdegree : C.degree u=d) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (c : Slice) (hc : accepts (d : ℚ) c₁ c₂ c=true)
    (y : ℝ) (hy : y ∈ Icc (c.lower : ℝ) (c.upper : ℝ)) :
    (c.bound : ℝ) ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  obtain ⟨ha,_,hcover⟩ := accepts_parts _ c₁ c₂ c hc
  have har : (0 : ℝ) < c.lower := by exact_mod_cast ha
  have hy0 := har.trans_le hy.1
  obtain ⟨s,hs,hps⟩ := ArmClasses.actual_parameter y hy0 p
  obtain ⟨t,ht,hqt⟩ := ArmClasses.actual_parameter y hy0 q
  rw [hp] at hps
  rw [hq] at hqt
  have hζ := (Focus.schur_in_disk C u y hy0).1
  rw [hdegree] at hζ
  have hdr : (0 : ℝ) < (d : ℚ) := by exact_mod_cast (by omega : 0 < d)
  have hh := FastArmCover.logarithm_lower (d : ℚ) c₁ c₂ c.lower c.upper c.bound c.cover
    0 1 0 1 hcover hdr y hy s t hs ht
    (by simpa only [Rat.cast_zero,Rat.cast_one] using hs)
    (by simpa only [Rat.cast_zero,Rat.cast_one] using ht)
    (RootSchur.schurScalar C u (Focus.z y))
    (by simpa only [Rat.cast_natCast] using hζ)
  rw [ClassGraphRemainders.actual_logarithm C u p q y hy0,hps,hqt]
  exact hh

theorem single_integral_lower (C : SimpleGraph V) (u : V) (p q d : ℕ) (hd : 1 ≤ d)
    (hdegree : C.degree u=d) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (c : Slice) (hc : accepts (d : ℚ) c₁ c₂ c=true) :
    ((c.upper : ℝ)-(c.lower : ℝ))*(c.bound : ℝ) ≤
      ∫ y : ℝ in (c.lower : ℝ)..(c.upper : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have ha : (0 : ℝ) < c.lower := by exact_mod_cast (accepts_parts _ c₁ c₂ c hc).1
  have hab : (c.lower : ℝ) ≤ c.upper := by exact_mod_cast (accepts_parts _ c₁ c₂ c hc).2.1.le
  have hfi := TailIntegral.interval_integrable_of_Ioi (logarithm_integrable C u p q 2) ha.le hab
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hfi
    (fun y hy => graph_lower C u p q d hd hdegree c₁ c₂ hp hq c hc y hy)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using h

/-- The exact rational sum of a contiguous sequence is paid by the actual
matrix logarithm on its physical interval. No gap or overlapping payment is
introduced by reciprocal ordinate coordinates. -/
theorem integral_lower (C : SimpleGraph V) (u : V) (p q d : ℕ) (hd : 1 ≤ d)
    (hdegree : C.degree u=d) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (a b : ℚ) (ha : 0 < a) (cs : List Slice) (h : checkAt (d : ℚ) c₁ c₂ a b cs=true) :
    (payment cs : ℝ) ≤ ∫ y : ℝ in (a : ℝ)..(b : ℝ),
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  induction cs generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true h
    subst b
    simp [payment]
  | cons c cs ih =>
    obtain ⟨he,hc,hr⟩ := cons_parts _ c₁ c₂ a b c cs h
    have hstep : c.lower < c.upper := (accepts_parts _ c₁ c₂ c hc).2.1
    rw [he] at hstep
    have hu : 0 < c.upper := ha.trans hstep
    have huB := endpoints_order _ c₁ c₂ c.upper b cs hr
    have h₁ := single_integral_lower C u p q d hd hdegree c₁ c₂ hp hq c hc
    rw [he] at h₁
    have h₂ := ih c.upper hu hr
    have hf := logarithm_integrable C u p q 2
    have har : (0 : ℝ) < a := by exact_mod_cast ha
    have hur : (0 : ℝ) < c.upper := by exact_mod_cast hu
    have haru : (a : ℝ) ≤ c.upper := by exact_mod_cast hstep.le
    have hurb : (c.upper : ℝ) ≤ b := by exact_mod_cast huB
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (TailIntegral.interval_integrable_of_Ioi hf har.le haru)
      (TailIntegral.interval_integrable_of_Ioi hf hur.le hurb)
    simp only [payment,Rat.cast_add,Rat.cast_mul,Rat.cast_sub,he]
    linarith only [h₁,h₂,hsum]

/-- Any paid class partition closes the exact original large degree-one
reserve for all physical arms classified by that one fixed class pair. -/
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1) (c₁ c₂ : Fin 5)
    (hp : ArmClasses.classify p=c₁) (hq : ArmClasses.classify q=c₂)
    (cs : List Slice)
    (hcheck : checkAt 1 c₁ c₂ (1/1000) 1024 cs=true)
    (hbudget : FastPaidDegreeOneClass.accepts (payment cs)=true) :
    (189/5000 : ℝ) < normalizedIntegral C u p q 2 := by
  let a : ℝ := ((1/1000 : ℚ) : ℝ)
  let Y : ℝ := ((1024 : ℚ) : ℝ)
  let B : ℝ := (payment cs : ℝ)
  have hc : checkAt ((1 : ℕ) : ℚ) c₁ c₂ (1/1000) 1024 cs=true := by
    simpa only [Nat.cast_one] using hcheck
  have hB := integral_lower C u p q 1 (by decide) hd c₁ c₂ hp hq
    (1/1000) 1024 (by norm_num) cs hc
  have hnorm := ClassGraphRemainders.normalized_lower_of_finite_payment C u p q
    (by omega) a Y B (by norm_num [a]) (by norm_num [a]) (by norm_num [Y]) hB
  have hl := RationalLog.sound (1/6250000) (-8) 23 32 FastPaidDegreeOneClass.origin_log_checked
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_neg] at hl
  rw [show (1/6250000 : ℝ)=(2*(1/1000 : ℝ)/5)^2 by norm_num,Real.log_pow] at hl
  have hlog : (-8 : ℝ) ≤ Real.log (2*a/5) := by
    dsimp [a]
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    linarith only [hl]
  have ho : (-9/1000 : ℝ) ≤ a*(Real.log (2*a/5)-1) := by
    have ha : a=(1/1000 : ℝ) := by norm_num [a]
    rw [ha] at hlog ⊢
    linarith only [hlog]
  have hb : (189/5000 : ℝ)*(22/7) < -9/1000+B-1/(2*Y) := by
    have hr := FastPaidDegreeOneClass.budget_sound _ hbudget
    convert hr using 1
    norm_num [B,Y]
  have hpi : Real.pi < (22/7 : ℝ) := lt_trans Real.pi_lt_d4 (by norm_num)
  have hraw : (189/5000 : ℝ)*Real.pi < a*(Real.log (2*a/5)-1)+B-1/(2*Y) := by
    nlinarith only [ho,hb,hpi]
  exact lt_of_lt_of_le ((lt_div_iff₀ Real.pi_pos).mpr hraw) hnorm

#print axioms normalized_target
#print axioms graph_lower
#print axioms single_integral_lower
#print axioms checked_cons
#print axioms cons_parts
#print axioms endpoints_order
#print axioms integral_lower
end
end Gebendorfer.RadenkovicGutman.FastArmCoverIntegral
