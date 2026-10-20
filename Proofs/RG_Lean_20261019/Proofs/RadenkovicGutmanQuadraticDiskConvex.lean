/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanQuadraticDisk

/-! Original convex Apollonius disk test, including the outside condition.
No low-strip polynomial signs are assumed proved by this generic lemma. -/
namespace Gebendorfer.RadenkovicGutman.QuadraticDisk
noncomputable section
set_option maxHeartbeats 0

def outside (a bx bt r : ℝ) (g : ℂ) : ℝ :=
  gradientSq a bx bt g-4*(a*r)^2

theorem convex_nonneg (a bx bt c r : ℝ) (g : ℂ) (ha : 0 < a) (hr : 0 ≤ r)
    (hO : 0 ≤ outside a bx bt r g) (hD : 0 ≤ directed a bx bt c r g)
    (hR : 0 ≤ reserve a bx bt c r g) (z : ℂ) (hz : ‖z-g‖ ≤ r) :
    0 ≤ value a bx bt c z := by
  let L := value a bx bt c g+a*r^2
  let qx := 2*a*g.re+bx
  let qt := 2*a*g.im+bt
  let dx := z.re-g.re
  let dy := z.im-g.im
  let K := Real.sqrt (qx^2+qt^2)
  let u := ‖z-g‖
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K^2=qx^2+qt^2 := Real.sq_sqrt (by positivity)
  have hu : 0 ≤ u := norm_nonneg _
  have hur : u ≤ r := hz
  have hu2 : dx^2+dy^2=u^2 := by
    simpa only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      pow_two,dx,dy,u] using (Complex.normSq_eq_norm_sq (z-g))
  have hD' : 0 ≤ 4*a*L := by simpa only [directed_identity,L] using hD
  have hL : 0 ≤ L := nonneg_of_mul_nonneg_right hD' (by positivity : 0 < 4*a)
  have hR' : 0 ≤ (16*a^2)*(L^2-r^2*(qx^2+qt^2)) := by
    have he : reserve a bx bt c r g = (16*a^2)*(L^2-r^2*(qx^2+qt^2)) := by
      unfold reserve
      rw [directed_identity]
      dsimp [gradientSq,L,qx,qt]
      ring
    rwa [he] at hR
  have hs : r^2*(qx^2+qt^2) ≤ L^2 := by
    have hn := nonneg_of_mul_nonneg_right hR' (by positivity : 0 < 16*a^2)
    linarith only [hn]
  have hLK : r*K ≤ L := by
    apply (sq_le_sq₀ (mul_nonneg hr hK) hL).mp
    rw [← hKsq] at hs
    nlinarith only [hs]
  have hOK : 2*a*r ≤ K := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ 2*a*r) hK).mp
    dsimp [outside,gradientSq,qx,qt] at hO hKsq ⊢
    nlinarith only [hO,hKsq]
  have hc : (qx*dx+qt*dy)^2 ≤ (qx^2+qt^2)*(dx^2+dy^2) := by
    nlinarith only [sq_nonneg (qx*dy-qt*dx)]
  have hlin : -(K*u) ≤ qx*dx+qt*dy := by
    have habs : |qx*dx+qt*dy| ≤ K*u := by
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK hu)).mp
      rw [sq_abs]
      rw [← hKsq,hu2] at hc
      nlinarith only [hc]
    exact (abs_le.mp habs).1
  have hfactor : 0 ≤ (r-u)*(K-a*(r+u)) := by
    apply mul_nonneg (sub_nonneg.mpr hur)
    have h := mul_nonneg ha.le (sub_nonneg.mpr hur)
    nlinarith only [hOK,h]
  have he : value a bx bt c z = L+(qx*dx+qt*dy)+a*(u^2-r^2) := by
    rw [← hu2]
    simp only [value,Complex.normSq_apply,L,qx,qt,dx,dy]
    ring
  rw [he]
  nlinarith only [hLK,hlin,hfactor]

#print axioms convex_nonneg
end
end Gebendorfer.RadenkovicGutman.QuadraticDisk
