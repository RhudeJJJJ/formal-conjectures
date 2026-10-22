/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01332 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000))
theorem leaf01332_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01332=true := by decide +kernel
#print axioms leaf01332_raw
theorem leaf01332_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01332=true := by decide +kernel
#print axioms leaf01332_rectangular
def affine01332 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01332 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01332_transform : affine01332=(NestedInteger.clearedAll 3 raw01332 (IntegerComputedClassCell.leftNumerator ![(11/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01332_transform
theorem leaf01332_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01332=true := by decide +kernel
#print axioms leaf01332_sign
theorem leaf01332_log : RationalLog.accepts (272131175/268435456) (29364075/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01332_log
def leaf01332 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(3/4)] ![(1/128),1,(1/8)] affine01332
theorem leaf01332_checked : FastNestedCellData.accepts 1 2 4 leaf01332=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (351284863/1000000000000) (272131175/268435456) (29364075/4294967296) 0 8 ![60,0,4] ![(11/128),0,(3/4)] ![(1/128),1,(1/8)] 1012509681988925272065310720000000000 1026810112935070886462778571654955008 2923012691654382177187004416000000000000 raw01332 affine01332
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01332_raw leaf01332_rectangular
    leaf01332_transform leaf01332_sign leaf01332_log
#print axioms leaf01332_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
