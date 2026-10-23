/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterWeightedPiece07
import Proofs.RadenkovicGutmanIntegerOuterPieces
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def outerSuffix07 : NestedInteger.Poly 3 := piece07
theorem outerSuffix07_eval (x : Fin 3 → ℝ) :
    NestedHorner.eval (NestedInteger.castPoly 3 outerSuffix07) x=
      NestedHorner.eval (NestedInteger.castPoly 3 (IntegerOuterTerms.transform 1 1 1024 84 source07)) x := by
  have h : segment07=source07 := by decide +kernel
  rw [outerSuffix07,piece07_identity,h]
#print axioms outerSuffix07_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
