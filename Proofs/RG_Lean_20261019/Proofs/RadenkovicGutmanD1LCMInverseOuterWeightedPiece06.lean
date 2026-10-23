/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanD1LCMInverseOuterWeightedData06
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem weights06_identity : weights06=IntegerWeightedOuter.weights 1 1 1024 72 segment06 := by decide +kernel
#print axioms weights06_identity
theorem piece06_weighted : piece06=IntegerWeightedOuter.applyWeights weights06 segment06 := by decide +kernel
#print axioms piece06_weighted
theorem piece06_identity : piece06=IntegerOuterTerms.transform 1 1 1024 72 segment06 :=
  IntegerWeightedOuter.checked 1 1 1024 72 segment06 piece06 weights06 weights06_identity piece06_weighted
#print axioms piece06_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
