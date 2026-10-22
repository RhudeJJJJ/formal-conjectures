/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00831 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 819422034728378102544479551488000000000000 206760600226112488099040440512645741674496 290910827636118115676944596992000000000000))
theorem leaf00831_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 819422034728378102544479551488000000000000 206760600226112488099040440512645741674496 290910827636118115676944596992000000000000 raw00831=true := by decide +kernel
#print axioms leaf00831_raw
theorem leaf00831_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00831=true := by decide +kernel
#print axioms leaf00831_rectangular
def affine00831 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00831 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00831_transform : affine00831=(NestedInteger.clearedAll 3 raw00831 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00831_transform
theorem leaf00831_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00831=true := by decide +kernel
#print axioms leaf00831_sign
theorem leaf00831_log : RationalLog.accepts (633486239/4294967296) (-4110199933/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00831_log
def leaf00831 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (177683830047/250000000000) (633486239/4294967296) (-4110199933/4294967296) 3 8 ![60,0,4] ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)] affine00831
theorem leaf00831_checked : FastNestedCellData.accepts 1 2 4 leaf00831=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (177683830047/250000000000) (633486239/4294967296) (-4110199933/4294967296) 3 8 ![60,0,4] ![(77/1600),0,(1/16)] ![(3/3200),1,(1/16)] 819422034728378102544479551488000000000000 206760600226112488099040440512645741674496 290910827636118115676944596992000000000000 raw00831 affine00831
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00831_raw leaf00831_rectangular
    leaf00831_transform leaf00831_sign leaf00831_log
#print axioms leaf00831_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
