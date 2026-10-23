/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterPiece03
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined04
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def outerSuffix03 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (1024^source04.length) piece03) outerSuffix04)
#print axioms outerSuffix03
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
