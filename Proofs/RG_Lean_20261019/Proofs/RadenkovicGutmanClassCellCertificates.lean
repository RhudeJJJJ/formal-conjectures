/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanScaledQuotient
import Proofs.RadenkovicGutmanRationalLog

/-! Exact cell certificates for the remaining fixed arm classes. Coefficient
acceptance, the representation of the three actual squared norms and the
logarithm payment are separate obligations. This module proves their sound
composition; the concrete cell partitions and integral ledgers remain required. -/
namespace Gebendorfer.RadenkovicGutman.ClassCellCertificates
open Focus
noncomputable section
set_option maxHeartbeats 0

def accepts {J : Type} [Fintype J] (cu cv cj : J → ℚ) (s L : ℚ) : Bool :=
  decide (0<s ∧ ∀ j, L*((1+s)*cu j+(1+1/s)*cv j)≤cj j)

theorem coefficient_sound {J : Type} [Fintype J] (cu cv cj : J → ℚ) (s L : ℚ)
    (hc : accepts cu cv cj s L=true) (w : J → ℝ) (hw : ∀ j, 0≤w j)
    (U V W : ℝ) (hu : U=∑ j, (cu j : ℝ)*w j)
    (hv : V=∑ j, (cv j : ℝ)*w j) (hj : W=∑ j, (cj j : ℝ)*w j) :
    (L : ℝ)*((1+(s : ℝ))*U+(1+1/(s : ℝ))*V)≤W := by
  have hcoeff : ∀ j, (L : ℝ)*((1+(s : ℝ))*(cu j : ℝ)+
      (1+1/(s : ℝ))*(cv j : ℝ))≤(cj j : ℝ) := by
    intro j
    exact_mod_cast (of_decide_eq_true hc).2 j
  calc
    _ = (L : ℝ)*((1+(s : ℝ))*(∑ j, (cu j : ℝ)*w j)+
        (1+1/(s : ℝ))*(∑ j, (cv j : ℝ)*w j)) := by rw [hu,hv]
    _ = ∑ j, ((L : ℝ)*((1+(s : ℝ))*(cu j : ℝ)+
        (1+1/(s : ℝ))*(cv j : ℝ)))*w j := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, (cj j : ℝ)*w j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcoeff j) (hw j))
    _ = W := hj.symm

theorem log_lower_of_square (L R : ℚ) (k n : ℕ)
    (hc : RationalLog.accepts L R k n=true) (z : ℂ) (hL : (L : ℝ)≤‖z‖^2) :
    (R : ℝ)≤Real.log ‖z‖ := by
  have hpos : (0 : ℝ)<L := by exact_mod_cast (of_decide_eq_true hc).1
  have hlog := Real.log_le_log hpos hL
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hR := RationalLog.sound L R k n hc
  linarith

theorem cell_log_lower {J : Type} [Fintype J]
    (cu cv cj : J → ℚ) (s L R : ℚ) (k n : ℕ)
    (hc : accepts cu cv cj s L=true) (hl : RationalLog.accepts L R k n=true)
    (w : J → ℝ) (hw : ∀ j, 0≤w j)
    (d y P Q : ℝ) (hd : 0<d) (hy : 0<y) (hP : y≤P) (hQ : y≤Q)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖≤r d y)
    (hu : ‖b d y P Q*star (e d y P Q)-a d P Q*star (c d y P Q)‖^2=
      ∑ j, (cu j : ℝ)*w j)
    (hv : ‖a d P Q*e d y P Q-b d y P Q*c d y P Q‖^2=
      ∑ j, (cv j : ℝ)*w j)
    (hj : (Complex.normSq (b d y P Q)-Complex.normSq (a d P Q))^2=
      ∑ j, (cj j : ℝ)*w j) :
    (R : ℝ)≤Real.log ‖quotient y P Q ζ‖ := by
  have hs : (0 : ℝ)<s := by exact_mod_cast (of_decide_eq_true hc).1
  have hcoeff := coefficient_sound cu cv cj s L hc w hw _ _ _ hu hv hj
  exact log_lower_of_square L R k n hl _
    (concrete_certificate d y P Q hd hy hP hQ ζ hζ s L hs hcoeff)

theorem coefficient_control : accepts (fun _ : Unit => 1) (fun _ => 1)
    (fun _ => 4) 1 1=true := by decide +kernel
theorem rejects_false_coefficient : accepts (fun _ : Unit => 1) (fun _ => 1)
    (fun _ => 3) 1 1=false := by decide +kernel

#print axioms coefficient_sound
#print axioms log_lower_of_square
#print axioms cell_log_lower
#print axioms coefficient_control
#print axioms rejects_false_coefficient
end
end Gebendorfer.RadenkovicGutman.ClassCellCertificates
