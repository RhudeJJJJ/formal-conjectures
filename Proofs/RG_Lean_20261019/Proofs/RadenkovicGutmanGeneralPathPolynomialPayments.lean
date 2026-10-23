/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathCellCertificates
import Proofs.RadenkovicGutmanLogPolynomialLower

namespace Gebendorfer.RadenkovicGutman.GeneralPathPolynomialPayments
open CoreQuotient Polynomial PolynomialPathMap RationalComplexPolynomial
open scoped Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The Young parameter and the norm payment may vary with the ordinate.
Multiplication by the positive parameter keeps all coefficient obligations polynomial. -/
theorem actual_norm_lower
    (x : ℚ) (y : ℝ) (hy : 0 < y) (p q : ℕ)
    (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es = true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep = true)
    (s L : ℝ) (hs : 0 < s)
    (hn : 0 < realEvaluator y (ofList ns))
    (he : 0 < realEvaluator y (ofList sep))
    (hbound : L * ((s+s^2)*realEvaluator y (ofList us) +
      (s+1)*realEvaluator y (ofList vs)) ≤ s*realEvaluator y (ofList js))
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u = 1) :
    L ≤ ‖(shifted (point x y) (source C u p q)).det /
      (shifted (point x y) (fused C u p q)).det‖^2 := by
  obtain ⟨ha,hb,hc,heval⟩ := GeneralPathPolynomials.accepts_sound x p q as bs cs es hpath y
  obtain ⟨huv,hvv,hjv,hnv,hev⟩ :=
    RationalMobiusPolynomials.accepts_sound as bs cs es us vs js ns sep hpoly y
  rw [hb,heval,ha,hc] at huv
  rw [ha,heval,hb,hc] at hvv
  rw [hb,ha] at hjv
  rw [hb,ha] at hnv
  rw [heval,hc] at hev
  rw [hnv] at hn
  rw [hev] at he
  have hscale (U V : ℝ) :
      (L*((1+s)*U+(1+1/s)*V))*s = L*((s+s^2)*U+(s+1)*V) := by
    field_simp [hs.ne']
    <;> ring
  have hbnd : L*((1+s)*realEvaluator y (ofList us)+
      (1+1/s)*realEvaluator y (ofList vs)) ≤ realEvaluator y (ofList js) := by
    apply (mul_le_mul_iff_right₀ hs).mp
    rw [hscale]
    simpa only [mul_comm s] using hbound
  rw [huv,hvv,hjv] at hbnd
  exact GeneralScaledQuotient.actual_norm_certificate C u hd x y hy p q s L hs he hn hbnd

#print axioms actual_norm_lower

/-- A rational polynomial payment for the logarithm of the actual determinant quotient. -/
theorem actual_log_lower
    (x : ℚ) (y : ℝ) (hy : 0 < y) (p q : ℕ)
    (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es = true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep = true)
    (s L : ℝ) (hs : 0 < s)
    (hn : 0 < realEvaluator y (ofList ns))
    (he : 0 < realEvaluator y (ofList sep))
    (hbound : L * ((s+s^2)*realEvaluator y (ofList us) +
      (s+1)*realEvaluator y (ofList vs)) ≤ s*realEvaluator y (ofList js))
    (c R : ℚ) (k n : ℕ) (hc : 0 < c) (hL : (c : ℝ) ≤ L)
    (hlog : RationalLog.accepts c R k n = true)
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u = 1) :
    (R : ℝ) + LogPolynomialLower.lowerFour (L/(c : ℝ)-1)/2 ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) x y := by
  exact LogPolynomialLower.rational_payment_lower _ L c R k n hc hL hlog
    (actual_norm_lower x y hy p q as bs cs es us vs js ns sep hpath hpoly
      s L hs hn he hbound C u hd)

#print axioms actual_log_lower

def paymentPolynomial (L : ℚ[X]) (c R : ℚ) : ℚ[X] :=
  let z := C (1/c)*L-1
  C R + (z-C (1/2)*z^2+C (1/3)*z^3-C (1/4)*z^4)*C (1/2)

theorem payment_evaluation (L : ℚ[X]) (c R : ℚ) (y : ℝ) :
    realEvaluator y (paymentPolynomial L c R) =
      (R : ℝ) + LogPolynomialLower.lowerFour (realEvaluator y L/(c : ℝ)-1)/2 := by
  simp only [paymentPolynomial,map_add,map_sub,map_mul,map_pow,map_one,real_C,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  unfold LogPolynomialLower.lowerFour
  ring

#print axioms payment_evaluation
end
end Gebendorfer.RadenkovicGutman.GeneralPathPolynomialPayments
