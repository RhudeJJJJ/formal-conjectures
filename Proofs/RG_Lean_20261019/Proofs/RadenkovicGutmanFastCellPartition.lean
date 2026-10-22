/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastCellGraphIntegral

namespace Gebendorfer.RadenkovicGutman.FastCellPartition
set_option maxHeartbeats 0

structure Slice where
  cell : FastNestedCellData.Cell
  lower : ℚ
  upper : ℚ

def accepts (d : ℚ) (c₁ c₂ : Fin 5) (c : Slice) : Bool :=
  FastNestedCellData.accepts d c₁ c₂ c.cell && FastPhysicalCell.shape c.cell c.lower c.upper

def checkAt (d : ℚ) (c₁ c₂ : Fin 5) : ℚ → ℚ → List Slice → Bool
  | a,b,[] => decide (a=b)
  | a,b,c::cs => decide (c.lower=a) && accepts d c₁ c₂ c && checkAt d c₁ c₂ c.upper b cs

def payment : List Slice → ℚ
  | [] => 0
  | c::cs => (c.upper-c.lower)*c.cell.payment+payment cs

theorem accepts_of_checks (d : ℚ) (c₁ c₂ : Fin 5) (c : Slice)
    (hc : FastNestedCellData.accepts d c₁ c₂ c.cell=true)
    (hs : FastPhysicalCell.shape c.cell c.lower c.upper=true) : accepts d c₁ c₂ c=true := by
  simpa only [accepts,Bool.and_eq_true] using And.intro hc hs

theorem accepts_parts (d : ℚ) (c₁ c₂ : Fin 5) (c : Slice) (h : accepts d c₁ c₂ c=true) :
    FastNestedCellData.accepts d c₁ c₂ c.cell=true ∧ FastPhysicalCell.shape c.cell c.lower c.upper=true := by
  simpa only [accepts,Bool.and_eq_true] using h

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
    obtain ⟨_,hshape⟩ := accepts_parts d c₁ c₂ c hc
    have hstep : c.lower < c.upper := (of_decide_eq_true hshape).2.1
    rw [he] at hstep
    exact hstep.le.trans (ih c.upper hr)

noncomputable section
open CoreQuotient Set MeasureTheory ActualFusionIntegral
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

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
    obtain ⟨hcell,hshape⟩ := accepts_parts _ c₁ c₂ c hc
    have hstep : c.lower < c.upper := (of_decide_eq_true hshape).2.1
    rw [he] at hstep
    have hu : 0 < c.upper := ha.trans hstep
    have huB := endpoints_order _ c₁ c₂ c.upper b cs hr
    have h₁ := FastCellGraphIntegral.integral_lower C u p q d hd hdegree c₁ c₂ hp hq
      c.cell c.lower c.upper hcell hshape
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

#print axioms checked_cons
#print axioms cons_parts
#print axioms endpoints_order
#print axioms integral_lower
end
end Gebendorfer.RadenkovicGutman.FastCellPartition
