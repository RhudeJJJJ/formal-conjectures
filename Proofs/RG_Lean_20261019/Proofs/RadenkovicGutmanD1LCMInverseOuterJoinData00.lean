/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterPiece00
import Proofs.RadenkovicGutmanD1LCMInverseOuterCombined01
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def affine01753 : NestedInteger.Poly 3 := rg_integer_data%
  (NestedInteger.add (NestedInteger.scale (1024^source01.length) piece00) outerSuffix01)
#print axioms affine01753
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
