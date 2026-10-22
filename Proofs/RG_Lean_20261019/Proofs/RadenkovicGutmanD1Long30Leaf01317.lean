/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01317 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000))
theorem leaf01317_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01317=true := by decide +kernel
#print axioms leaf01317_raw
theorem leaf01317_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01317=true := by decide +kernel
#print axioms leaf01317_rectangular
def affine01317 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01317 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/64),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01317_transform : affine01317=(NestedInteger.clearedAll 3 raw01317 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/64),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01317_transform
theorem leaf01317_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01317=true := by decide +kernel
#print axioms leaf01317_sign
theorem leaf01317_log : RationalLog.accepts (4388082687/4294967296) (46060185/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01317_log
def leaf01317 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,(3/4)] ![(1/128),1,(1/8)] affine01317
theorem leaf01317_checked : FastNestedCellData.accepts 1 2 4 leaf01317=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (138292753/200000000000) (4388082687/4294967296) (46060185/4294967296) 0 8 ![60,0,4] ![(7/64),0,(3/4)] ![(1/128),1,(1/8)] 510210204367945763074447769600000000000 521632061435269607472036905339131527168 754388136933349801015295292211200000000000 raw01317 affine01317
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01317_raw leaf01317_rectangular
    leaf01317_transform leaf01317_sign leaf01317_log
#print axioms leaf01317_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
