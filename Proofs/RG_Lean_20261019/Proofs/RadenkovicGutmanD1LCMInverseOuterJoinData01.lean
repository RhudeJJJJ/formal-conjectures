/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterPiece01
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined02
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def outerSuffix01 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (1024^source02.length) piece01) outerSuffix02)
#print axioms outerSuffix01
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
