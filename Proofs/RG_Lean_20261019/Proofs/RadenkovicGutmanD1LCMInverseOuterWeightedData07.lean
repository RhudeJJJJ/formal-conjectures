/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerBernsteinRows
import Proofs.RadenkovicGutmanD1LCMInverseOuterSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def weights07 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 1 1 1024 84 segment07)
def piece07 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerWeightedOuter.applyWeights weights07 segment07)
#print axioms weights07
#print axioms piece07
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
