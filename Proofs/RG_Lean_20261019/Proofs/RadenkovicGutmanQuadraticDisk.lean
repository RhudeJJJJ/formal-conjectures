/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailHalfGeometry

/-! The original correlated Apollonius quadratic on a closed disk.
Source: rg_multiarm_direct_escape_certificate.py, build_polynomials.
The directed sign and complete squared reserve are retained. -/
namespace Gebendorfer.RadenkovicGutman.QuadraticDisk
noncomputable section
set_option maxHeartbeats 0

def value (a bx bt c : ℝ) (z : ℂ) : ℝ :=
  a*Complex.normSq z+bx*z.re+bt*z.im+c
def gradientSq (a bx bt : ℝ) (g : ℂ) : ℝ :=
  (2*a*g.re+bx)^2+(2*a*g.im+bt)^2
def directed (a bx bt c r : ℝ) (g : ℂ) : ℝ :=
  gradientSq a bx bt g+4*(a*r)^2+4*a*c-bx^2-bt^2
def reserve (a bx bt c r : ℝ) (g : ℂ) : ℝ :=
  (directed a bx bt c r g)^2-16*(a*r)^2*gradientSq a bx bt g

theorem directed_identity (a bx bt c r : ℝ) (g : ℂ) :
    directed a bx bt c r g = 4*a*(value a bx bt c g+a*r^2) := by
  simp only [directed,gradientSq,value,Complex.normSq_apply]
  ring

theorem disk_coordinates (z g : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ‖z-g‖ ≤ r) : (z.re-g.re)^2+(z.im-g.im)^2 ≤ r^2 := by
  have h : ‖z-g‖^2 ≤ r^2 := by nlinarith only [hr,hz,norm_nonneg (z-g)]
  rw [← Complex.normSq_eq_norm_sq] at h
  simpa only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,pow_two] using h

/-- Strict concavity, the original directed sign and the full error square
imply the bound on every point of the same closed disk. -/
theorem concave_nonneg (a bx bt c r : ℝ) (g : ℂ) (ha : a < 0) (hr : 0 ≤ r)
    (hD : directed a bx bt c r g ≤ 0) (hR : 0 ≤ reserve a bx bt c r g)
    (z : ℂ) (hz : ‖z-g‖ ≤ r) : 0 ≤ value a bx bt c z := by
  let L := value a bx bt c g+a*r^2
  let qx := 2*a*g.re+bx
  let qt := 2*a*g.im+bt
  let dx := z.re-g.re
  let dy := z.im-g.im
  have hD' : 4*a*L ≤ 0 := by simpa only [directed_identity,L] using hD
  have hL : 0 ≤ L := by nlinarith only [hD',ha]
  have hR' : 0 ≤ (16*a^2)*(L^2-r^2*(qx^2+qt^2)) := by
    have he : reserve a bx bt c r g = (16*a^2)*(L^2-r^2*(qx^2+qt^2)) := by
      unfold reserve
      rw [directed_identity]
      dsimp [gradientSq,L,qx,qt]
      ring
    rwa [he] at hR
  have hs : r^2*(qx^2+qt^2) ≤ L^2 := by
    have hn := nonneg_of_mul_nonneg_right hR' (by nlinarith [sq_pos_of_ne_zero (ne_of_lt ha)] : 0 < 16*a^2)
    linarith only [hn]
  have hd : dx^2+dy^2 ≤ r^2 := disk_coordinates z g r hr hz
  have hc : (qx*dx+qt*dy)^2 ≤ (qx^2+qt^2)*(dx^2+dy^2) := by
    nlinarith only [sq_nonneg (qx*dy-qt*dx)]
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ qx^2+qt^2 by positivity)
  have hsq : (qx*dx+qt*dy)^2 ≤ L^2 := by nlinarith only [hc,hm,hs]
  have habs : |qx*dx+qt*dy| ≤ L :=
    (sq_le_sq₀ (abs_nonneg _) hL).mp (by simpa only [sq_abs] using hsq)
  have hlin := (abs_le.mp habs).1
  have hquad := mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr hd)
  have he : value a bx bt c z = L+(qx*dx+qt*dy)+a*(dx^2+dy^2-r^2) := by
    simp only [value,Complex.normSq_apply,L,qx,qt,dx,dy]
    ring
  rw [he]
  linarith only [hlin,hquad]

#print axioms directed_identity
#print axioms disk_coordinates
#print axioms concave_nonneg
end
end Gebendorfer.RadenkovicGutman.QuadraticDisk
