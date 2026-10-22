/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00115 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 354014060027288530607897418137600000000000 283900998735182231838425309216790632464384 2958667271878838559203380953088000000000000))
theorem leaf00115_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 354014060027288530607897418137600000000000 283900998735182231838425309216790632464384 2958667271878838559203380953088000000000000 raw00115=true := by decide +kernel
#print axioms leaf00115_raw
theorem leaf00115_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00115=true := by decide +kernel
#print axioms leaf00115_rectangular
def affine00115 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00115 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00115_transform : affine00115=(NestedInteger.clearedAll 3 raw00115 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00115_transform
theorem leaf00115_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00115=true := by decide +kernel
#print axioms leaf00115_sign
theorem leaf00115_log : RationalLog.accepts (3142774855/4294967296) (-167685099/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00115_log
def leaf00115 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (95955703243/1000000000000) (3142774855/4294967296) (-167685099/1073741824) 1 8 ![52,0,4] ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)] affine00115
theorem leaf00115_checked : FastNestedCellData.accepts 1 0 4 leaf00115=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (95955703243/1000000000000) (3142774855/4294967296) (-167685099/1073741824) 1 8 ![52,0,4] ![(1/80),0,(1/4)] ![(1/1600),1,(1/4)] 354014060027288530607897418137600000000000 283900998735182231838425309216790632464384 2958667271878838559203380953088000000000000 raw00115 affine00115
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00115_raw leaf00115_rectangular
    leaf00115_transform leaf00115_sign leaf00115_log
#print axioms leaf00115_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
