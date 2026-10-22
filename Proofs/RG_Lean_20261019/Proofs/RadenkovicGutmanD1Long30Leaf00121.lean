/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00121 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 808992359173424181761510735872000000000 661243045974714868461084231177408086016 7538872958008295805916545024000000000000))
theorem leaf00121_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 808992359173424181761510735872000000000 661243045974714868461084231177408086016 7538872958008295805916545024000000000000 raw00121=true := by decide +kernel
#print axioms leaf00121_raw
theorem leaf00121_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00121=true := by decide +kernel
#print axioms leaf00121_rectangular
def affine00121 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00121 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00121_transform : affine00121=(NestedInteger.clearedAll 3 raw00121 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00121_transform
theorem leaf00121_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00121=true := by decide +kernel
#print axioms leaf00121_sign
theorem leaf00121_log : RationalLog.accepts (1613737875/2147483648) (-613629767/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00121_log
def leaf00121 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43855563667/500000000000) (1613737875/2147483648) (-613629767/4294967296) 1 8 ![60,0,4] ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)] affine00121
theorem leaf00121_checked : FastNestedCellData.accepts 1 2 4 leaf00121=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43855563667/500000000000) (1613737875/2147483648) (-613629767/4294967296) 1 8 ![60,0,4] ![(11/4000),0,(1/16)] ![(3/32000),1,(1/16)] 808992359173424181761510735872000000000 661243045974714868461084231177408086016 7538872958008295805916545024000000000000 raw00121 affine00121
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00121_raw leaf00121_rectangular
    leaf00121_transform leaf00121_sign leaf00121_log
#print axioms leaf00121_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
