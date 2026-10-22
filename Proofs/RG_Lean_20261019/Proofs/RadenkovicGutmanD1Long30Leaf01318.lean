/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01318 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000))
theorem leaf01318_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01318=true := by decide +kernel
#print axioms leaf01318_raw
theorem leaf01318_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01318=true := by decide +kernel
#print axioms leaf01318_rectangular
def affine01318 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01318 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/64),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01318_transform : affine01318=(NestedInteger.clearedAll 3 raw01318 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/64),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01318_transform
theorem leaf01318_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01318=true := by decide +kernel
#print axioms leaf01318_sign
theorem leaf01318_log : RationalLog.accepts (4388082687/4294967296) (46060185/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01318_log
def leaf01318 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,(7/8)] ![(1/128),1,(1/16)] affine01318
theorem leaf01318_checked : FastNestedCellData.accepts 1 2 4 leaf01318=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,(7/8)] ![(1/128),1,(1/16)] 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01318 affine01318
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01318_raw leaf01318_rectangular
    leaf01318_transform leaf01318_sign leaf01318_log
#print axioms leaf01318_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
