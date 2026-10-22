/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00921 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 52298831172019581208307433472000000000000 16348485833239766352789728045963436621824 22525026447181228519888781312000000000000))
theorem leaf00921_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 52298831172019581208307433472000000000000 16348485833239766352789728045963436621824 22525026447181228519888781312000000000000 raw00921=true := by decide +kernel
#print axioms leaf00921_raw
theorem leaf00921_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00921=true := by decide +kernel
#print axioms leaf00921_rectangular
def affine00921 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00921 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00921_transform : affine00921=(NestedInteger.clearedAll 3 raw00921 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00921_transform
theorem leaf00921_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00921=true := by decide +kernel
#print axioms leaf00921_sign
theorem leaf00921_log : RationalLog.accepts (97244927/536870912) (-3669029309/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00921_log
def leaf00921 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (362896040801/500000000000) (97244927/536870912) (-3669029309/4294967296) 3 8 ![60,0,4] ![(5/64),0,(1/16)] ![(1/320),1,(1/16)] affine00921
theorem leaf00921_checked : FastNestedCellData.accepts 1 2 4 leaf00921=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (362896040801/500000000000) (97244927/536870912) (-3669029309/4294967296) 3 8 ![60,0,4] ![(5/64),0,(1/16)] ![(1/320),1,(1/16)] 52298831172019581208307433472000000000000 16348485833239766352789728045963436621824 22525026447181228519888781312000000000000 raw00921 affine00921
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00921_raw leaf00921_rectangular
    leaf00921_transform leaf00921_sign leaf00921_log
#print axioms leaf00921_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
