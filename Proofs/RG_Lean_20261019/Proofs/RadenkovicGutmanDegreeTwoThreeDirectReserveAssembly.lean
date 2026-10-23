/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeClassAssembly
import Proofs.RadenkovicGutmanActualArmSymmetry

namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeDirectReserveAssembly
open ArmClasses DegreeTwoThreeThresholds DegreeTwoThreeClassAssembly
open ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- Fifteen unordered actual-graph reserve certificates for a fixed degree.
The denominator is the original class-specific cutoff. -/
def ClassCertificates (d : ℕ) : Prop :=
  ∀ (a b : Fin 5), a ≤ b →
    ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
      C.degree u=d → classify p=a → classify q=b →
        (2 : ℝ)/(cutoff d (a,b) : ℝ)<normalizedIntegral C u p q 2

theorem threshold_swap (d p q : ℕ) : threshold d p q=threshold d q p := by
  unfold threshold
  split_ifs
  · exact table2_symmetric _ _
  · exact table3_symmetric _ _

/-- Swapping actual arms supplies the other fifteen ordered cases. -/
theorem normalized_reserve (d : ℕ) (h : ClassCertificates d)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hd : C.degree u=d) :
    (2 : ℝ)/(threshold d p q : ℝ)<normalizedIntegral C u p q 2 := by
  rcases le_total (classify p) (classify q) with hle | hle
  · have hr := h (classify p) (classify q) hle m C u p q hd rfl rfl
    simpa only [threshold,cutoff] using hr
  · rw [ActualArmSymmetry.normalized_swap_two C u p q,threshold_swap d p q]
    have hr := h (classify q) (classify p) hle m C u q p hd rfl rfl
    simpa only [threshold,cutoff] using hr

/-- Preserve the complete original finite branch and all thirty class reserves. -/
theorem input_family (h2 : ClassCertificates 2) (h3 : ClassCertificates 3)
    (hFinite : DegreeTwoThreeClassAssembly.FiniteCases)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (CoreQuotient.source C u p q).IsTree) (hd : C.degree u=2 ∨ C.degree u=3) :
    0<meanIntegral C u p q := by
  by_cases hcut : order C p q<threshold (C.degree u) p q
  · exact hFinite m C u p q hT hd hcut
  · have hroot : 1≤C.degree u := by rcases hd with h | h <;> omega
    have hpositive : 0<threshold (C.degree u) p q := by
      unfold threshold
      split_ifs
      · exact table2_positive _ _
      · exact table3_positive _ _
    have hr : (2 : ℝ)/(threshold (C.degree u) p q : ℝ)<
        normalizedIntegral C u p q 2 := by
      rcases hd with h | h
      · simpa only [h] using normalized_reserve 2 h2 m C u p q h
      · simpa only [h] using normalized_reserve 3 h3 m C u p q h
    exact (strict_iff_mean_integral_pos C u p q hT hroot).mp
      (strict_of_cutoff_reserve C u p q (threshold (C.degree u) p q)
        hT hroot hpositive (by omega) hr)

#print axioms threshold_swap
#print axioms normalized_reserve
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeDirectReserveAssembly
