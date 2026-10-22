/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00825 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4047005807649461834810153500672000000000000 326410433706074084999420676370387735412736 371954601731944421809037770752000000000000))
theorem leaf00825_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4047005807649461834810153500672000000000000 326410433706074084999420676370387735412736 371954601731944421809037770752000000000000 raw00825=true := by decide +kernel
#print axioms leaf00825_raw
theorem leaf00825_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00825=true := by decide +kernel
#print axioms leaf00825_rectangular
def affine00825 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00825 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00825_transform : affine00825=(NestedInteger.clearedAll 3 raw00825 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00825_transform
theorem leaf00825_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00825=true := by decide +kernel
#print axioms leaf00825_sign
theorem leaf00825_log : RationalLog.accepts (92250243/2147483648) (-6759306153/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00825_log
def leaf00825 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (877554497743/1000000000000) (92250243/2147483648) (-6759306153/4294967296) 5 8 ![60,0,4] ![(151/3200),0,0] ![(3/3200),1,(1/16)] affine00825
theorem leaf00825_checked : FastNestedCellData.accepts 1 2 4 leaf00825=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (877554497743/1000000000000) (92250243/2147483648) (-6759306153/4294967296) 5 8 ![60,0,4] ![(151/3200),0,0] ![(3/3200),1,(1/16)] 4047005807649461834810153500672000000000000 326410433706074084999420676370387735412736 371954601731944421809037770752000000000000 raw00825 affine00825
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00825_raw leaf00825_rectangular
    leaf00825_transform leaf00825_sign leaf00825_log
#print axioms leaf00825_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
