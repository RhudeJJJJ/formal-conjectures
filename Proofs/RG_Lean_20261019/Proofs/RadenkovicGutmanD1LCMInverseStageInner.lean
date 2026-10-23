/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseStageRaw
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def inner01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerAffineStages.inner raw01753 ![1,0,0] ![1,1,1] ![1024,1,1])
theorem leaf01753_inner : inner01753=(IntegerAffineStages.inner raw01753 ![1,0,0] ![1,1,1] ![1024,1,1]) := by decide +kernel
#print axioms leaf01753_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
