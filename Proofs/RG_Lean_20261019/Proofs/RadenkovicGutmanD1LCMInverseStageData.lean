/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerScaledCell
import Proofs.RadenkovicGutmanD1IntegerNorm00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000))

#print axioms raw01753
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
