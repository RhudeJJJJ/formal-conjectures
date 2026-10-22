/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualArmSymmetry

namespace Gebendorfer.RadenkovicGutman.DegreeOneClassDispatch
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

def ClassCertificate (a b : Fin 5) : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    C.degree u=1 → ArmClasses.classify p=a → ArmClasses.classify q=b →
      (189/5000 : ℝ) < normalizedIntegral C u p q 2

structure Certificates : Prop where
  class00 : ClassCertificate 0 0
  class01 : ClassCertificate 0 1
  class02 : ClassCertificate 0 2
  class03 : ClassCertificate 0 3
  class04 : ClassCertificate 0 4
  class11 : ClassCertificate 1 1
  class12 : ClassCertificate 1 2
  class13 : ClassCertificate 1 3
  class14 : ClassCertificate 1 4
  class22 : ClassCertificate 2 2
  class23 : ClassCertificate 2 3
  class24 : ClassCertificate 2 4
  class33 : ClassCertificate 3 3
  class34 : ClassCertificate 3 4
  class44 : ClassCertificate 4 4

/-- The fifteen unordered classes cover both orders of every actual arm pair. -/
theorem normalized_target (h : Certificates) (m : ℕ) (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hd : C.degree u=1) :
    (189/5000 : ℝ) < normalizedIntegral C u p q 2 := by
  have dispatch (a b : Fin 5) (hp : ArmClasses.classify p=a)
      (hq : ArmClasses.classify q=b) :
      (189/5000 : ℝ) < normalizedIntegral C u p q 2 := by
    fin_cases a <;> fin_cases b
    · exact h.class00 m C u p q hd hp hq
    · exact h.class01 m C u p q hd hp hq
    · exact h.class02 m C u p q hd hp hq
    · exact h.class03 m C u p q hd hp hq
    · exact h.class04 m C u p q hd hp hq
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class01 m C u q p hd hq hp
    · exact h.class11 m C u p q hd hp hq
    · exact h.class12 m C u p q hd hp hq
    · exact h.class13 m C u p q hd hp hq
    · exact h.class14 m C u p q hd hp hq
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class02 m C u q p hd hq hp
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class12 m C u q p hd hq hp
    · exact h.class22 m C u p q hd hp hq
    · exact h.class23 m C u p q hd hp hq
    · exact h.class24 m C u p q hd hp hq
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class03 m C u q p hd hq hp
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class13 m C u q p hd hq hp
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class23 m C u q p hd hq hp
    · exact h.class33 m C u p q hd hp hq
    · exact h.class34 m C u p q hd hp hq
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class04 m C u q p hd hq hp
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class14 m C u q p hd hq hp
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class24 m C u q p hd hq hp
    · rw [ActualArmSymmetry.normalized_swap_two C u p q]
      exact h.class34 m C u q p hd hq hp
    · exact h.class44 m C u p q hd hp hq
  exact dispatch _ _ rfl rfl

#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.DegreeOneClassDispatch
