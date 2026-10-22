/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01113 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8622330356587609179222022553600000000000 10261001793891692456023635728165612027904 54881356374608137408327817625600000000000))
theorem leaf01113_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8622330356587609179222022553600000000000 10261001793891692456023635728165612027904 54881356374608137408327817625600000000000 raw01113=true := by decide +kernel
#print axioms leaf01113_raw
theorem leaf01113_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01113=true := by decide +kernel
#print axioms leaf01113_rectangular
def affine01113 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01113 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/32),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01113_transform : affine01113=(NestedInteger.clearedAll 3 raw01113 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/32),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01113_transform
theorem leaf01113_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01113=true := by decide +kernel
#print axioms leaf01113_sign
theorem leaf01113_log : RationalLog.accepts (2153060983/2147483648) (696263/536870912) 0 8=true := by decide +kernel
#print axioms leaf01113_log
def leaf01113 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18696698609/100000000000) (2153060983/2147483648) (696263/536870912) 0 8 ![60,0,4] ![(19/32),0,(7/8)] ![(1/32),1,(1/16)] affine01113
theorem leaf01113_checked : FastNestedCellData.accepts 1 2 4 leaf01113=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18696698609/100000000000) (2153060983/2147483648) (696263/536870912) 0 8 ![60,0,4] ![(19/32),0,(7/8)] ![(1/32),1,(1/16)] 8622330356587609179222022553600000000000 10261001793891692456023635728165612027904 54881356374608137408327817625600000000000 raw01113 affine01113
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01113_raw leaf01113_rectangular
    leaf01113_transform leaf01113_sign leaf01113_log
#print axioms leaf01113_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
