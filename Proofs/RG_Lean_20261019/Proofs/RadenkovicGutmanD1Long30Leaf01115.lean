/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01115 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 206475350979102541021657956352000000000000 249574395362071618927038167858288049258496 1393578875385013681090774171648000000000000))
theorem leaf01115_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 206475350979102541021657956352000000000000 249574395362071618927038167858288049258496 1393578875385013681090774171648000000000000 raw01115=true := by decide +kernel
#print axioms leaf01115_raw
theorem leaf01115_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01115=true := by decide +kernel
#print axioms leaf01115_rectangular
def affine01115 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01115 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/16),1,(1/2)]))
theorem leaf01115_transform : affine01115=(NestedInteger.clearedAll 3 raw01115 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01115_transform
theorem leaf01115_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01115=true := by decide +kernel
#print axioms leaf01115_sign
theorem leaf01115_log : RationalLog.accepts (1100741051/1073741824) (6666341/536870912) 0 8=true := by decide +kernel
#print axioms leaf01115_log
def leaf01115 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (179088819277/1000000000000) (1100741051/1073741824) (6666341/536870912) 0 8 ![60,0,4] ![(5/8),0,0] ![(1/16),1,(1/2)] affine01115
theorem leaf01115_checked : FastNestedCellData.accepts 1 2 4 leaf01115=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (179088819277/1000000000000) (1100741051/1073741824) (6666341/536870912) 0 8 ![60,0,4] ![(5/8),0,0] ![(1/16),1,(1/2)] 206475350979102541021657956352000000000000 249574395362071618927038167858288049258496 1393578875385013681090774171648000000000000 raw01115 affine01115
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01115_raw leaf01115_rectangular
    leaf01115_transform leaf01115_sign leaf01115_log
#print axioms leaf01115_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
