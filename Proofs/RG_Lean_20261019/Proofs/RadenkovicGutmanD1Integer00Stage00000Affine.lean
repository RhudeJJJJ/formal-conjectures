/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Integer00Stage00000Inner
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def affine00000 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedOuter ((IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) 0) ((IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) 0) ((IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) 0) inner00000)
theorem leaf00000_outer : affine00000=(NestedInteger.clearedOuter ((IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) 0) ((IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) 0) ((IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) 0) inner00000) := by decide +kernel
#print axioms leaf00000_outer
theorem leaf00000_transform : affine00000=NestedInteger.clearedAll 3 raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) :=
  IntegerAffineStages.checked raw00000 inner00000 affine00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]) leaf00000_inner leaf00000_outer
#print axioms leaf00000_transform
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
