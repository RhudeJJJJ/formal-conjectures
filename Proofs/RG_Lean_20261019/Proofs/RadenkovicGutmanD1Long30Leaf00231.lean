/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00231 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1390041502909965289096310947840000000000 991294478004263809377525729680651452416 6577557396360191214531851059200000000000))
theorem leaf00231_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1390041502909965289096310947840000000000 991294478004263809377525729680651452416 6577557396360191214531851059200000000000 raw00231=true := by decide +kernel
#print axioms leaf00231_raw
theorem leaf00231_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00231=true := by decide +kernel
#print axioms leaf00231_rectangular
def affine00231 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00231 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00231_transform : affine00231=(NestedInteger.clearedAll 3 raw00231 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00231_transform
theorem leaf00231_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00231=true := by decide +kernel
#print axioms leaf00231_sign
theorem leaf00231_log : RationalLog.accepts (1330881615/2147483648) (-4013573/16777216) 1 8=true := by decide +kernel
#print axioms leaf00231_log
def leaf00231 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15070860173/100000000000) (1330881615/2147483648) (-4013573/16777216) 1 8 ![60,0,4] ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)] affine00231
theorem leaf00231_checked : FastNestedCellData.accepts 1 2 4 leaf00231=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15070860173/100000000000) (1330881615/2147483648) (-4013573/16777216) 1 8 ![60,0,4] ![(77/16000),0,(1/16)] ![(3/32000),1,(1/16)] 1390041502909965289096310947840000000000 991294478004263809377525729680651452416 6577557396360191214531851059200000000000 raw00231 affine00231
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00231_raw leaf00231_rectangular
    leaf00231_transform leaf00231_sign leaf00231_log
#print axioms leaf00231_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
