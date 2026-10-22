/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01244 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 106362449169084084178091245568000000000000 115593544151434215652523245637399155310592 20047719305003989326565478498304000000000000))
theorem leaf01244_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 106362449169084084178091245568000000000000 115593544151434215652523245637399155310592 20047719305003989326565478498304000000000000 raw01244=true := by decide +kernel
#print axioms leaf01244_raw
theorem leaf01244_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01244=true := by decide +kernel
#print axioms leaf01244_rectangular
def affine01244 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01244 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/64),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01244_transform : affine01244=(NestedInteger.clearedAll 3 raw01244 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/64),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01244_transform
theorem leaf01244_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01244=true := by decide +kernel
#print axioms leaf01244_sign
theorem leaf01244_log : RationalLog.accepts (4640963963/4294967296) (166383069/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01244_log
def leaf01244 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (5765919923/1000000000000) (4640963963/4294967296) (166383069/4294967296) 0 8 ![60,0,4] ![(15/64),0,(15/16)] ![(1/64),1,(1/16)] affine01244
theorem leaf01244_checked : FastNestedCellData.accepts 1 2 4 leaf01244=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (5765919923/1000000000000) (4640963963/4294967296) (166383069/4294967296) 0 8 ![60,0,4] ![(15/64),0,(15/16)] ![(1/64),1,(1/16)] 106362449169084084178091245568000000000000 115593544151434215652523245637399155310592 20047719305003989326565478498304000000000000 raw01244 affine01244
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01244_raw leaf01244_rectangular
    leaf01244_transform leaf01244_sign leaf01244_log
#print axioms leaf01244_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
