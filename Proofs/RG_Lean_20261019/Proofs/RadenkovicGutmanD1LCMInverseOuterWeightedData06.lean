/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def weights06 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 1 1 1024 72 segment06)
def piece06 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerWeightedOuter.applyWeights weights06 segment06)
#print axioms weights06
#print axioms piece06
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
