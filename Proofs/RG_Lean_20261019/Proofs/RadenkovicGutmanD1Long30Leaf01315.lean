/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01315 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000))
theorem leaf01315_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01315=true := by decide +kernel
#print axioms leaf01315_raw
theorem leaf01315_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01315=true := by decide +kernel
#print axioms leaf01315_rectangular
def affine01315 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01315 (IntegerComputedClassCell.leftNumerator ![(7/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/64),0,0] ![(1/128),1,(1/2)]))
theorem leaf01315_transform : affine01315=(NestedInteger.clearedAll 3 raw01315 (IntegerComputedClassCell.leftNumerator ![(7/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/64),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01315_transform
theorem leaf01315_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01315=true := by decide +kernel
#print axioms leaf01315_sign
theorem leaf01315_log : RationalLog.accepts (4388082687/4294967296) (46060185/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01315_log
def leaf01315 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,0] ![(1/128),1,(1/2)] affine01315
theorem leaf01315_checked : FastNestedCellData.accepts 1 2 4 leaf01315=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,0] ![(1/128),1,(1/2)] 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01315 affine01315
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01315_raw leaf01315_rectangular
    leaf01315_transform leaf01315_sign leaf01315_log
#print axioms leaf01315_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
