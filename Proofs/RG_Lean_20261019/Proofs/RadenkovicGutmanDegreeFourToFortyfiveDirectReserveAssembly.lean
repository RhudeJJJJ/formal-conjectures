/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalAssembly
import Proofs.RadenkovicGutmanActualArmSymmetry

namespace Gebendorfer.RadenkovicGutman.DegreeFourToFortyfiveDirectReserveAssembly
open ArmClasses ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

def ClassCertificates (d : ℕ) : Prop :=
  ∀ (a b : Fin 5), a ≤ b →
    ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
      C.degree u=d → classify p=a → classify q=b →
        (2/13 : ℝ)<normalizedIntegral C u p q 2

/-- Each unordered certificate applies to both orders of the actual arms. -/
theorem normalized_reserve (d : ℕ) (h : ClassCertificates d)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hd : C.degree u=d) : (2/13 : ℝ)<normalizedIntegral C u p q 2 := by
  rcases le_total (classify p) (classify q) with hle | hle
  · exact h _ _ hle m C u p q hd rfl rfl
  · rw [ActualArmSymmetry.normalized_swap_two C u p q]
    exact h _ _ hle m C u q p hd rfl rfl

/-- All forty-two degrees and fifteen unordered classes remain required.
The conclusion retains the original tree and order quantifiers. -/
theorem input_family (h : ∀ d, 4≤d → d≤45 → ClassCertificates d)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (_hT : (CoreQuotient.source C u p q).IsTree)
    (h4 : 4≤C.degree u) (h45 : C.degree u≤45) (_hN : 13≤order C p q) :
    (2/13 : ℝ)<normalizedIntegral C u p q 2 :=
  normalized_reserve (C.degree u) (h _ h4 h45) m C u p q rfl

#print axioms normalized_reserve
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.DegreeFourToFortyfiveDirectReserveAssembly
