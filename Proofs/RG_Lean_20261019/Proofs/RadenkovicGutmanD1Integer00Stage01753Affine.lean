/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Integer00Stage01753Inner
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def affine01753 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedOuter ((IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) 0) ((IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) 0) ((IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]) 0) inner01753)
theorem leaf01753_outer : affine01753=(NestedInteger.clearedOuter ((IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) 0) ((IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) 0) ((IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]) 0) inner01753) := by decide +kernel
#print axioms leaf01753_outer
theorem leaf01753_transform : affine01753=NestedInteger.clearedAll 3 raw01753 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]) :=
  IntegerAffineStages.checked raw01753 inner01753 affine01753 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/1024),1,1]) leaf01753_inner leaf01753_outer
#print axioms leaf01753_transform
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
