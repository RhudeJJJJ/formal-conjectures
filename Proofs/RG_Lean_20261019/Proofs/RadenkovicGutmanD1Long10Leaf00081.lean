/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00081 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3743466965276039116621562773504000000000000 3093313569813589445989711135898104496128 15242972434745797689802227712000000000000))
theorem leaf00081_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3743466965276039116621562773504000000000000 3093313569813589445989711135898104496128 15242972434745797689802227712000000000000 raw00081=true := by decide +kernel
#print axioms leaf00081_raw
theorem leaf00081_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00081=true := by decide +kernel
#print axioms leaf00081_rectangular
def affine00081 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00081 (IntegerComputedClassCell.leftNumerator ![(7/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/800),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00081_transform : affine00081=(NestedInteger.clearedAll 3 raw00081 (IntegerComputedClassCell.leftNumerator ![(7/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/800),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00081_transform
theorem leaf00081_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00081=true := by decide +kernel
#print axioms leaf00081_sign
theorem leaf00081_log : RationalLog.accepts (2950313/4294967296) (-3910185543/1073741824) 11 8=true := by decide +kernel
#print axioms leaf00081_log
def leaf00081 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (202933750819/1000000000000) (2950313/4294967296) (-3910185543/1073741824) 11 8 ![52,0,4] ![(7/800),0,0] ![(1/3200),1,(1/4)] affine00081
theorem leaf00081_checked : FastNestedCellData.accepts 1 0 4 leaf00081=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (202933750819/1000000000000) (2950313/4294967296) (-3910185543/1073741824) 11 8 ![52,0,4] ![(7/800),0,0] ![(1/3200),1,(1/4)] 3743466965276039116621562773504000000000000 3093313569813589445989711135898104496128 15242972434745797689802227712000000000000 raw00081 affine00081
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00081_raw leaf00081_rectangular
    leaf00081_transform leaf00081_sign leaf00081_log
#print axioms leaf00081_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
