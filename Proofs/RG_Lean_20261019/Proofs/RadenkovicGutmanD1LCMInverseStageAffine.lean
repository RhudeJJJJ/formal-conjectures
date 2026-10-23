/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseStageInner
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def affine01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerOuterTerms.transform 1 1 1024 0 inner01753)
theorem leaf01753_outer : affine01753=(IntegerOuterTerms.transform 1 1 1024 0 inner01753) := by decide +kernel
#print axioms leaf01753_outer
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
