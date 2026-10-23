/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterPiece02
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined03
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def outerSuffix02 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (1024^source03.length) piece02) outerSuffix03)
#print axioms outerSuffix02
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
