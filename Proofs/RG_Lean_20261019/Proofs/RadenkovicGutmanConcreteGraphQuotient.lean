/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The concrete Mobius quotient is the genuine two-arm graph determinant ratio
for all positive arm lengths and all residual root degrees.
-/
import Proofs.RadenkovicGutmanQuotientBridge

namespace Gebendorfer.RadenkovicGutman.Focus

open Matrix CoreQuotient PathRecurrence PathEnclosure
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_from_rho (y : ℝ) (hy : 0 < y) (n : ℕ) :
    resolventQuotient (z y) (n + 1) =
      1 - (1 + Complex.I * (rho y n : ℂ)) / z y := by
  have h := path_resolvent_real y hy n
  have he : (2 + Complex.I * (y : ℂ)) = z y := by unfold z; ring
  rw [he] at h
  have hz : z y ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp [z] at hi
    linarith
  apply (eq_sub_iff_add_eq).mpr
  field_simp [hz]
  linear_combination -h

theorem schur_in_disk (C : SimpleGraph V) (u : V) (y : ℝ) (hy : 0 < y) :
    ‖RootSchur.schurScalar C u (z y) - g (C.degree u) y‖ ≤ r (C.degree u) y ∧
      RootSchur.schurScalar C u (z y) ≠ 0 := by
  have hz : 0 < (z y).im := by simpa [z] using hy
  have h := RootSchur.graph_schur_disk C u (z y) hz
  have hg : z y - (C.degree u : ℂ) +
      ((C.degree u : ℝ) / (2 * y) : ℝ) * Complex.I = g (C.degree u) y := by
    unfold z g
    push_cast
    ring
  have hzre : (z y).im = y := by simp [z]
  rw [hzre, hg] at h
  constructor
  · exact h.1
  · intro he
    rw [he] at h
    have hi := h.2
    simp at hi
    linarith

/-- The arbitrary-core determinant formula in the exact coordinates consumed
by the concrete polynomial certificates, with no separation premise left. -/
theorem concrete_graph_quotient (C : SimpleGraph V) (u : V)
    (y : ℝ) (hy : 0 < y) (p q : ℕ) :
    (shifted (z y) (source C u p q)).det /
        (shifted (z y) (fused C u p q)).det =
      quotient y (rho y p) (rho y q) (RootSchur.schurScalar C u (z y)) := by
  have hz : (z y).im ≠ 0 := by simpa [z] using hy.ne'
  have h := normalized_resolvent_quotient (z y) hz C u p q
  dsimp only at h
  have hs := schur_in_disk C u y hy
  have hm : rho y (p + q + 1) = m y (rho y p) (rho y q) := rho_addition y hy p q
  rw [h, endpoint_from_rho y hy p, endpoint_from_rho y hy q,
    show p + q + 2 = (p + q + 1) + 1 by omega, endpoint_from_rho y hy (p + q + 1),
    hm, RootSchur.root_resolvent_schur C u (z y) (by simpa [z] using hy)]
  exact normalized_mobius y (rho y p) (rho y q) hy
    (rho_ge y hy p) (rho_ge y hy q) _ hs.2

#print axioms endpoint_from_rho
#print axioms concrete_graph_quotient

end
end Gebendorfer.RadenkovicGutman.Focus
