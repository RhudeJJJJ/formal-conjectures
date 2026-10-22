/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01319 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000))
theorem leaf01319_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01319=true := by decide +kernel
#print axioms leaf01319_raw
theorem leaf01319_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01319=true := by decide +kernel
#print axioms leaf01319_rectangular
def affine01319 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01319 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/64),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01319_transform : affine01319=(NestedInteger.clearedAll 3 raw01319 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/64),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01319_transform
theorem leaf01319_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01319=true := by decide +kernel
#print axioms leaf01319_sign
theorem leaf01319_log : RationalLog.accepts (4388082687/4294967296) (46060185/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01319_log
def leaf01319 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,(15/16)] ![(1/128),1,(1/16)] affine01319
theorem leaf01319_checked : FastNestedCellData.accepts 1 2 4 leaf01319=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,(15/16)] ![(1/128),1,(1/16)] 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01319 affine01319
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01319_raw leaf01319_rectangular
    leaf01319_transform leaf01319_sign leaf01319_log
#print axioms leaf01319_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
