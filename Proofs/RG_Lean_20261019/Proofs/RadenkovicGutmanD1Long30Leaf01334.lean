/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01334 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000))
theorem leaf01334_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01334=true := by decide +kernel
#print axioms leaf01334_raw
theorem leaf01334_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01334=true := by decide +kernel
#print axioms leaf01334_rectangular
def affine01334 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01334 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01334_transform : affine01334=(NestedInteger.clearedAll 3 raw01334 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01334_transform
theorem leaf01334_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01334=true := by decide +kernel
#print axioms leaf01334_sign
theorem leaf01334_log : RationalLog.accepts (272131175/268435456) (29364075/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01334_log
def leaf01334 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(15/16)] ![(1/128),1,(1/16)] affine01334
theorem leaf01334_checked : FastNestedCellData.accepts 1 2 4 leaf01334=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(15/16)] ![(1/128),1,(1/16)] 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01334 affine01334
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01334_raw leaf01334_rectangular
    leaf01334_transform leaf01334_sign leaf01334_log
#print axioms leaf01334_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
