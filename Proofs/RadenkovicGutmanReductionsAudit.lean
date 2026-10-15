/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exact-type and negative controls for the algebraic RG reductions.
There is deliberately no global RG theorem in this partial development.
-/
import Proofs.RadenkovicGutmanFusionQuotient
import Proofs.RadenkovicGutmanResolventDisk
import Proofs.RadenkovicGutmanArmBridge
import Proofs.RadenkovicGutmanPathAudit

namespace Gebendorfer.RadenkovicGutman.ReductionsAudit

open Matrix CoreQuotient PathRecurrence
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The determinant-ratio endpoint, with graph Laplacians written explicitly. -/
theorem exact_graph_quotient (z : ℂ) (hz : z.im ≠ 0)
    (C : SimpleGraph V) (u : V) (p q : ℕ) :
    let hp := resolventQuotient z (p + 1)
    let hq := resolventQuotient z (q + 1)
    let hr := resolventQuotient z (p + q + 2)
    let k := (z • (1 : Matrix V V ℂ) - C.lapMatrix ℂ)⁻¹ u u
    let A₀ := (1 - hp) * (1 - hq)
    let B₀ := 2 - hp - hq
    let C₀ := 1 - hr
    det (z • 1 - (source C u p q).lapMatrix ℂ) /
      det (z • 1 - (fused C u p q).lapMatrix ℂ) =
        ((A₀ - B₀ * k) / (A₀ - B₀ * (1 / z))) *
        ((C₀ - 1 / z) / (C₀ - k)) := by
  exact normalized_resolvent_quotient z hz C u p q

/-- The raw path determinant prefactor is not identically one. It must be
cancelled by singleton normalization, not silently discarded. -/
theorem normalization_negative_control :
    let z : ℂ := 2 + Complex.I
    den z 1 * den z 1 / den z 2 ≠ 1 := by
  dsimp only
  have hz : (2 + Complex.I : ℂ).im ≠ 0 := by norm_num
  have hn := den_ne_zero_of_im_ne_zero (2 + Complex.I) hz 1
  intro he
  have h := (div_eq_one_iff_eq hn).mp he
  have hi := congrArg Complex.im h
  norm_num [den_succ, num_succ, num_zero, den_zero, Complex.mul_im, Complex.mul_re] at hi

#print axioms exact_graph_quotient
#print axioms normalization_negative_control
#print axioms PathEnclosure.all_long_path_resolvents
#print axioms ResolventDisk.hermitian_resolvent_disk

end Gebendorfer.RadenkovicGutman.ReductionsAudit
