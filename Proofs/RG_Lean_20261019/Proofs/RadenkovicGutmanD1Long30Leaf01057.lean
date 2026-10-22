/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01057 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 283649529632455759053131979161600000000000 264715324797198704496456469037324074745856 688615398763430338380444362342400000000000))
theorem leaf01057_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 283649529632455759053131979161600000000000 264715324797198704496456469037324074745856 688615398763430338380444362342400000000000 raw01057=true := by decide +kernel
#print axioms leaf01057_raw
theorem leaf01057_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01057=true := by decide +kernel
#print axioms leaf01057_rectangular
def affine01057 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01057 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01057_transform : affine01057=(NestedInteger.clearedAll 3 raw01057 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01057_transform
theorem leaf01057_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01057=true := by decide +kernel
#print axioms leaf01057_sign
theorem leaf01057_log : RationalLog.accepts (2895276319/4294967296) (-423444481/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01057_log
def leaf01057 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (76883359063/200000000000) (2895276319/4294967296) (-423444481/2147483648) 1 8 ![60,0,4] ![(47/160),0,(1/8)] ![(3/160),1,(1/8)] affine01057
theorem leaf01057_checked : FastNestedCellData.accepts 1 2 4 leaf01057=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (76883359063/200000000000) (2895276319/4294967296) (-423444481/2147483648) 1 8 ![60,0,4] ![(47/160),0,(1/8)] ![(3/160),1,(1/8)] 283649529632455759053131979161600000000000 264715324797198704496456469037324074745856 688615398763430338380444362342400000000000 raw01057 affine01057
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01057_raw leaf01057_rectangular
    leaf01057_transform leaf01057_sign leaf01057_log
#print axioms leaf01057_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
