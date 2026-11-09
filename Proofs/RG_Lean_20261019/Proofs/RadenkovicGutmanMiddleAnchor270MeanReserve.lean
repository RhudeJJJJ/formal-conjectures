/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate270

/-!
# Actual-mean reserve for original Anchor270

The original certificate and source/fused pair are unchanged. Both arm
orientations are retained. Core degree one and physical order at most 52 imply
physical order 50, 51 or 52. Transport from the certificate threshold leaves
an actual-mean reserve greater than 9/100 and an energy gap greater than 9/50.

Sources: original Anchor270 certificate and ActualFusionIntegral.anchor_transport.
This endpoint concerns one anchor, not the complete Middle family.
-/
namespace Gebendorfer.RadenkovicGutman.MiddleAnchor270MeanReserve
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Exact threshold displacement for every possible physical order. -/
theorem threshold_displacement (n : ℕ) (h50 : 50 ≤ n) (h52 : n ≤ 52) :
    |(2 : ℝ) / (n : ℝ) - 2 / 52| ≤ 1 / 650 := by
  interval_cases n <;> norm_num

/-- A strict payment remains after the largest possible threshold shift. -/
theorem original_payment_reserve :
    (9 / 100 : ℝ) + 1 / 650 <
      (MiddleOriginalAnchorCertificate270.anchor.lower : ℝ) := by
  norm_num [MiddleOriginalAnchorCertificate270.anchor]

/-- Transfer a certified bound to positivity at the actual mean. -/
theorem quantitative_anchor_transport {m : ℕ}
    (C : SimpleGraph (Fin m)) (u : Fin m) (p q a : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (L eps : ℝ)
    (hcert : L ≤ normalizedIntegral C u p q (2 - 2 / (a : ℝ)))
    (hshift : |2 / (order C p q : ℝ) - 2 / (a : ℝ)| ≤ eps)
    (hmargin : eps < L) :
    0 < meanIntegral C u p q := by
  have ht := anchor_transport C u p q a hT hd
  change normalizedIntegral C u p q (2 - 2 / (a : ℝ)) -
    |2 / (order C p q : ℝ) - 2 / (a : ℝ)| ≤ meanIntegral C u p q at ht
  linarith

/-- Transfer a certified bound while retaining an explicit strict surplus. -/
theorem quantitative_anchor_transport_strict {m : ℕ}
    (C : SimpleGraph (Fin m)) (u : Fin m) (p q a : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (L eps margin : ℝ)
    (hcert : L ≤ normalizedIntegral C u p q (2 - 2 / (a : ℝ)))
    (hshift : |2 / (order C p q : ℝ) - 2 / (a : ℝ)| ≤ eps)
    (hmargin : margin + eps < L) :
    margin < meanIntegral C u p q := by
  have ht := anchor_transport C u p q a hT hd
  change normalizedIntegral C u p q (2 - 2 / (a : ℝ)) -
    |2 / (order C p q : ℝ) - 2 / (a : ℝ)| ≤ meanIntegral C u p q at ht
  linarith

/-- Actual-mean reserve with the original tree hypotheses and both orientations. -/
theorem actual_mean_reserve {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) (hT : (source C u p q).IsTree) (hd : C.degree u = 1)
    (hor : (p = 0 ∧ q = 46) ∨ (p = 46 ∧ q = 0))
    (h52 : order C p q ≤ 52) :
    (9 / 100 : ℝ) < meanIntegral C u p q := by
  have hdeg : C.degree u < m := by
    simpa only [Fintype.card_fin] using C.degree_lt_card_verts u
  have hsum : p + q = 46 := by rcases hor with h | h <;> omega
  have horder : order C p q = m + p + q + 2 := by
    simp only [order, Fintype.card_sum, Fintype.card_fin]
    omega
  have h50 : 50 ≤ order C p q := by omega
  have hbound := MiddleOriginalAnchorCertificate270.certificate m C u p q hT hd
    (by simpa only [MiddleOriginalAnchorCertificate270.anchor] using hor)
    (by simpa only [MiddleOriginalAnchorCertificate270.anchor] using h52)
  change (MiddleOriginalAnchorCertificate270.anchor.lower : ℝ) ≤
    normalizedIntegral C u p q (2 - 2 / 52) at hbound
  have hshift := threshold_displacement (order C p q) h50 h52
  exact quantitative_anchor_transport_strict C u p q 52 hT (by omega)
    (MiddleOriginalAnchorCertificate270.anchor.lower : ℝ) (1 / 650) (9 / 100)
    hbound hshift original_payment_reserve

/-- Quantitative energy decrease for the unchanged original source/fused pair. -/
theorem actual_energy_gap {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) (hT : (source C u p q).IsTree) (hd : C.degree u = 1)
    (hor : (p = 0 ∧ q = 46) ∨ (p = 46 ∧ q = 0))
    (h52 : order C p q ≤ 52) :
    (9 / 50 : ℝ) < laplacianEnergy (source C u p q) -
      laplacianEnergy (fused C u p q) := by
  have hreserve := actual_mean_reserve C u p q hT hd hor h52
  have hid := energy_difference C u p q hT (by omega)
  change laplacianEnergy (source C u p q) - laplacianEnergy (fused C u p q) =
    2 * meanIntegral C u p q at hid
  linarith

/-- Strict fusion at the actual mean, without substituting threshold two. -/
theorem strict_fusion {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) (hT : (source C u p q).IsTree) (hd : C.degree u = 1)
    (hor : (p = 0 ∧ q = 46) ∨ (p = 46 ∧ q = 0))
    (h52 : order C p q ≤ 52) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  have hgap := actual_energy_gap C u p q hT hd hor h52
  linarith

#print axioms quantitative_anchor_transport
#print axioms quantitative_anchor_transport_strict
#print axioms threshold_displacement
#print axioms original_payment_reserve
#print axioms actual_mean_reserve
#print axioms actual_energy_gap
#print axioms strict_fusion
end
end Gebendorfer.RadenkovicGutman.MiddleAnchor270MeanReserve
