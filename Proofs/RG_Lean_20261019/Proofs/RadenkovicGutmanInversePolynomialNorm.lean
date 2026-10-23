/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathPolynomialPayments

namespace Gebendorfer.RadenkovicGutman.InversePolynomialNorm
noncomputable section

theorem inverse_parameter (U V J M L : ℝ) (hM : 0 < M)
    (hb : L*((M+1)*U+(M^2+M)*V) ≤ M*J) :
    L*((1/M+(1/M)^2)*U+(1/M+1)*V) ≤ (1/M)*J := by
  calc
    _ = (L*((M+1)*U+(M^2+M)*V))/(M^2) := by
      field_simp [hM.ne']
      ring
    _ ≤ (M*J)/(M^2) := div_le_div_of_nonneg_right hb (sq_nonneg M)
    _ = _ := by field_simp [hM.ne']

theorem reserve_bound (D J M K y : ℝ) (hy : 0 < y)
    (hP : 0 ≤ y^2*(M*J-D)-K*D) : (1+K/y^2)*D ≤ M*J := by
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hy)).mp
  have he : y^2*((1+K/y^2)*D) = (y^2+K)*D := by field_simp [hy.ne']
  rw [he]
  nlinarith only [hP]

#print axioms inverse_parameter
#print axioms reserve_bound
end
end Gebendorfer.RadenkovicGutman.InversePolynomialNorm
