/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01330 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000))
theorem leaf01330_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01330=true := by decide +kernel
#print axioms leaf01330_raw
theorem leaf01330_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01330=true := by decide +kernel
#print axioms leaf01330_rectangular
def affine01330 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01330 (IntegerComputedClassCell.leftNumerator ![(11/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01330_transform : affine01330=(NestedInteger.clearedAll 3 raw01330 (IntegerComputedClassCell.leftNumerator ![(11/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01330_transform
theorem leaf01330_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01330=true := by decide +kernel
#print axioms leaf01330_sign
theorem leaf01330_log : RationalLog.accepts (272131175/268435456) (29364075/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01330_log
def leaf01330 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,0] ![(1/128),1,(1/2)] affine01330
theorem leaf01330_checked : FastNestedCellData.accepts 1 2 4 leaf01330=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,0] ![(1/128),1,(1/2)] 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01330 affine01330
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01330_raw leaf01330_rectangular
    leaf01330_transform leaf01330_sign leaf01330_log
#print axioms leaf01330_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
