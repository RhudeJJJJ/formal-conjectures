/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01193 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 13450972978192385485622476800000000000 15948701792999262754264973813772976128 719478426834441199669372518400000000000))
theorem leaf01193_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 13450972978192385485622476800000000000 15948701792999262754264973813772976128 719478426834441199669372518400000000000 raw01193=true := by decide +kernel
#print axioms leaf01193_raw
theorem leaf01193_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01193=true := by decide +kernel
#print axioms leaf01193_rectangular
def affine01193 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01193 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/32),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01193_transform : affine01193=(NestedInteger.clearedAll 3 raw01193 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/32),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01193_transform
theorem leaf01193_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01193=true := by decide +kernel
#print axioms leaf01193_sign
theorem leaf01193_log : RationalLog.accepts (1245516937/1073741824) (19918055/268435456) 0 8=true := by decide +kernel
#print axioms leaf01193_log
def leaf01193 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2216703267/100000000000) (1245516937/1073741824) (19918055/268435456) 0 8 ![60,0,4] ![(13/32),0,(7/8)] ![(1/32),1,(1/16)] affine01193
theorem leaf01193_checked : FastNestedCellData.accepts 1 2 4 leaf01193=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2216703267/100000000000) (1245516937/1073741824) (19918055/268435456) 0 8 ![60,0,4] ![(13/32),0,(7/8)] ![(1/32),1,(1/16)] 13450972978192385485622476800000000000 15948701792999262754264973813772976128 719478426834441199669372518400000000000 raw01193 affine01193
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01193_raw leaf01193_rectangular
    leaf01193_transform leaf01193_sign leaf01193_log
#print axioms leaf01193_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
