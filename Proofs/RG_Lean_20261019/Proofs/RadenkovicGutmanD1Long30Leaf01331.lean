/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01331 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000))
theorem leaf01331_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01331=true := by decide +kernel
#print axioms leaf01331_raw
theorem leaf01331_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01331=true := by decide +kernel
#print axioms leaf01331_rectangular
def affine01331 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01331 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01331_transform : affine01331=(NestedInteger.clearedAll 3 raw01331 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01331_transform
theorem leaf01331_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01331=true := by decide +kernel
#print axioms leaf01331_sign
theorem leaf01331_log : RationalLog.accepts (272131175/268435456) (29364075/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01331_log
def leaf01331 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(1/2)] ![(1/128),1,(1/4)] affine01331
theorem leaf01331_checked : FastNestedCellData.accepts 1 2 4 leaf01331=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(1/2)] ![(1/128),1,(1/4)] 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01331 affine01331
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01331_raw leaf01331_rectangular
    leaf01331_transform leaf01331_sign leaf01331_log
#print axioms leaf01331_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
