/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Integer00Stage01753Raw
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def inner01753 : NestedInteger.Poly 3 := rg_integer_data% (IntegerAffineStages.inner raw01753 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]))
theorem leaf01753_inner : inner01753=(IntegerAffineStages.inner raw01753 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf01753_inner
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
