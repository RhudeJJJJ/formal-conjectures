/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01351 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 543246236677204833468416000000000000 543744573606266556118654030222196736 96164926326101757057940062208000000000000))
theorem leaf01351_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 543246236677204833468416000000000000 543744573606266556118654030222196736 96164926326101757057940062208000000000000 raw01351=true := by decide +kernel
#print axioms leaf01351_raw
theorem leaf01351_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01351=true := by decide +kernel
#print axioms leaf01351_rectangular
def affine01351 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01351 (IntegerComputedClassCell.leftNumerator ![(11/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(11/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(11/512),0,0] ![(1/512),1,1]))
theorem leaf01351_transform : affine01351=(NestedInteger.clearedAll 3 raw01351 (IntegerComputedClassCell.leftNumerator ![(11/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(11/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(11/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01351_transform
theorem leaf01351_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01351=true := by decide +kernel
#print axioms leaf01351_sign
theorem leaf01351_log : RationalLog.accepts (2149441449/2147483648) (1956909/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01351_log
def leaf01351 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1413573/250000000000) (2149441449/2147483648) (1956909/4294967296) 0 8 ![60,0,4] ![(11/512),0,0] ![(1/512),1,1] affine01351
theorem leaf01351_checked : FastNestedCellData.accepts 1 2 4 leaf01351=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1413573/250000000000) (2149441449/2147483648) (1956909/4294967296) 0 8 ![60,0,4] ![(11/512),0,0] ![(1/512),1,1] 543246236677204833468416000000000000 543744573606266556118654030222196736 96164926326101757057940062208000000000000 raw01351 affine01351
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01351_raw leaf01351_rectangular
    leaf01351_transform leaf01351_sign leaf01351_log
#print axioms leaf01351_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
