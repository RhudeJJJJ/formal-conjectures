/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exact-type audits and boundary controls for the all-length path bridge. -/
import Proofs.RadenkovicGutmanPathResolvent

namespace Gebendorfer.RadenkovicGutman.PathAudit
open Matrix Gebendorfer.RadenkovicGutman.PathRecurrence

theorem exact_determinant (z : ℂ) (n : ℕ) :
    Matrix.det (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      (SimpleGraph.pathGraph (n + 1)).lapMatrix ℂ) = den z (n + 1) :=
  pathMatrix_det z n

theorem exact_resolvent (z : ℂ) (n : ℕ) :
    (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      (SimpleGraph.pathGraph (n + 1)).lapMatrix ℂ)⁻¹ 0 0 =
        num z (n + 1) / den z (n + 1) :=
  pathMatrix_inv_endpoint z n

theorem exact_upper_half_plane (z : ℂ) (hz : 0 < z.im) (n : ℕ) :
    (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      (SimpleGraph.pathGraph (n + 1)).lapMatrix ℂ) *
    (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) -
      (SimpleGraph.pathGraph (n + 1)).lapMatrix ℂ)⁻¹ = 1 :=
  pathMatrix_mul_inverse z (ne_of_gt hz) n

/-- The one-vertex path has degree zero, not the degree of a terminal vertex of P2. -/
theorem singleton_control (z : ℚ) : det (pathMatrix z 1) = z := by
  rw [pathMatrix_det z 0]
  simp

/-- A grounded three-vertex tridiagonal matrix differs from the full path matrix. -/
theorem endpoint_degree_negative_control :
    det (tridiagonal (fun _ : Fin 3 => (2 : ℚ))) ≠ det (pathMatrix (4 : ℚ) 3) := by
  rw [Matrix.det_fin_three, pathMatrix_det (4 : ℚ) 2]
  norm_num [tridiagonal, Fin.ext_iff, num, den, state]

#print axioms exact_determinant
#print axioms exact_resolvent
#print axioms exact_upper_half_plane
#print axioms singleton_control
#print axioms endpoint_degree_negative_control
end Gebendorfer.RadenkovicGutman.PathAudit
