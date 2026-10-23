/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterPiece04
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined05
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def outerSuffix04 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (1024^source05.length) piece04) outerSuffix05)
#print axioms outerSuffix04
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
