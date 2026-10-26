/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPositiveTail
namespace Gebendorfer.RadenkovicGutman.PositiveTailParts
open scoped Classical
theorem checks_of_parts (d : ComputedGeneralPathData.Data) (K Y : ℚ)
    (hK : 0≤K) (hY : 0<Y)
    (hP : ComputedHornerArithmetic.nonnegative
      (ComputedPositiveTail.shifted (ComputedPositiveTail.comparison d K) Y)=true)
    (hN : ComputedHornerArithmetic.nonnegative (ComputedPositiveTail.shifted d.N Y)=true)
    (hE : ComputedHornerArithmetic.nonnegative (ComputedPositiveTail.shifted d.E Y)=true)
    (hN0 : 0<(ComputedPositiveTail.shifted d.N Y).headD 0)
    (hE0 : 0<(ComputedPositiveTail.shifted d.E Y).headD 0) :
    ComputedPositiveTail.checks d K Y=true := by
  rw [ComputedPositiveTail.checks,decide_eq_true_eq]
  exact ⟨hK,hY,hP,hN,hE,hN0,hE0⟩
#print axioms checks_of_parts
end Gebendorfer.RadenkovicGutman.PositiveTailParts
