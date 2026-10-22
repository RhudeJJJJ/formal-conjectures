/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00106 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33109786169036610273359691776000000000000 27585376729111375493603140765099866718208 349292764505057223086138458112000000000000))
theorem leaf00106_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33109786169036610273359691776000000000000 27585376729111375493603140765099866718208 349292764505057223086138458112000000000000 raw00106=true := by decide +kernel
#print axioms leaf00106_raw
theorem leaf00106_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00106=true := by decide +kernel
#print axioms leaf00106_rectangular
def affine00106 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00106 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00106_transform : affine00106=(NestedInteger.clearedAll 3 raw00106 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00106_transform
theorem leaf00106_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00106=true := by decide +kernel
#print axioms leaf00106_sign
theorem leaf00106_log : RationalLog.accepts (1658215801/2147483648) (-277620857/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00106_log
def leaf00106 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (78974944609/1000000000000) (1658215801/2147483648) (-277620857/2147483648) 1 8 ![60,0,4] ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00106
theorem leaf00106_checked : FastNestedCellData.accepts 1 2 4 leaf00106=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (78974944609/1000000000000) (1658215801/2147483648) (-277620857/2147483648) 1 8 ![60,0,4] ![(79/32000),0,(1/16)] ![(3/32000),1,(1/16)] 33109786169036610273359691776000000000000 27585376729111375493603140765099866718208 349292764505057223086138458112000000000000 raw00106 affine00106
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00106_raw leaf00106_rectangular
    leaf00106_transform leaf00106_sign leaf00106_log
#print axioms leaf00106_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
