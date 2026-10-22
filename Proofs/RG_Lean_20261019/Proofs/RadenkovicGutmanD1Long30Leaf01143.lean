/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01143 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 398391252146079707921206004940800000000000 507527632394352024088211430176137215475712 4700019036402669810855075381248000000000000))
theorem leaf01143_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 398391252146079707921206004940800000000000 507527632394352024088211430176137215475712 4700019036402669810855075381248000000000000 raw01143=true := by decide +kernel
#print axioms leaf01143_raw
theorem leaf01143_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01143=true := by decide +kernel
#print axioms leaf01143_rectangular
def affine01143 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01143 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01143_transform : affine01143=(NestedInteger.clearedAll 3 raw01143 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/16),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01143_transform
theorem leaf01143_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01143=true := by decide +kernel
#print axioms leaf01143_sign
theorem leaf01143_log : RationalLog.accepts (4938285635/4294967296) (149866755/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01143_log
def leaf01143 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (107984165269/1000000000000) (4938285635/4294967296) (149866755/2147483648) 0 8 ![60,0,4] ![(15/16),0,(7/8)] ![(1/16),1,(1/16)] affine01143
theorem leaf01143_checked : FastNestedCellData.accepts 1 2 4 leaf01143=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (107984165269/1000000000000) (4938285635/4294967296) (149866755/2147483648) 0 8 ![60,0,4] ![(15/16),0,(7/8)] ![(1/16),1,(1/16)] 398391252146079707921206004940800000000000 507527632394352024088211430176137215475712 4700019036402669810855075381248000000000000 raw01143 affine01143
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01143_raw leaf01143_rectangular
    leaf01143_transform leaf01143_sign leaf01143_log
#print axioms leaf01143_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
