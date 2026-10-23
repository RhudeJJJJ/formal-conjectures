/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanD1LCMInverseOuterWeightedData07
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem weights07_identity : weights07=IntegerWeightedOuter.weights 1 1 1024 84 segment07 := by decide +kernel
#print axioms weights07_identity
theorem piece07_weighted : piece07=IntegerWeightedOuter.applyWeights weights07 segment07 := by decide +kernel
#print axioms piece07_weighted
theorem piece07_identity : piece07=IntegerOuterTerms.transform 1 1 1024 84 segment07 :=
  IntegerWeightedOuter.checked 1 1 1024 84 segment07 piece07 weights07 weights07_identity piece07_weighted
#print axioms piece07_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
