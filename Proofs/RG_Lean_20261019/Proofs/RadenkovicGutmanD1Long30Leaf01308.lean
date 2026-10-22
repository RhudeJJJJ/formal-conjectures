/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01308 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 741189671440862164289165721600000000000 762507401363300461076878504754814124032 759092007308437498612807421132800000000000))
theorem leaf01308_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 741189671440862164289165721600000000000 762507401363300461076878504754814124032 759092007308437498612807421132800000000000 raw01308=true := by decide +kernel
#print axioms leaf01308_raw
theorem leaf01308_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01308=true := by decide +kernel
#print axioms leaf01308_rectangular
def affine01308 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01308 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/8),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01308_transform : affine01308=(NestedInteger.clearedAll 3 raw01308 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/8),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01308_transform
theorem leaf01308_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01308=true := by decide +kernel
#print axioms leaf01308_sign
theorem leaf01308_log : RationalLog.accepts (4414063093/4294967296) (58737243/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01308_log
def leaf01308 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (200899863/200000000000) (4414063093/4294967296) (58737243/4294967296) 0 8 ![60,0,4] ![(1/8),0,(7/8)] ![(1/128),1,(1/16)] affine01308
theorem leaf01308_checked : FastNestedCellData.accepts 1 2 4 leaf01308=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (200899863/200000000000) (4414063093/4294967296) (58737243/4294967296) 0 8 ![60,0,4] ![(1/8),0,(7/8)] ![(1/128),1,(1/16)] 741189671440862164289165721600000000000 762507401363300461076878504754814124032 759092007308437498612807421132800000000000 raw01308 affine01308
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01308_raw leaf01308_rectangular
    leaf01308_transform leaf01308_sign leaf01308_log
#print axioms leaf01308_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
