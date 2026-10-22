/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00837 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2398360390852072002576168517632000000000000 927383141323835626409958422742284718047232 1783218186424840352822517039104000000000000))
theorem leaf00837_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2398360390852072002576168517632000000000000 927383141323835626409958422742284718047232 1783218186424840352822517039104000000000000 raw00837=true := by decide +kernel
#print axioms leaf00837_raw
theorem leaf00837_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00837=true := by decide +kernel
#print axioms leaf00837_rectangular
def affine00837 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00837 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00837_transform : affine00837=(NestedInteger.clearedAll 3 raw00837 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00837_transform
theorem leaf00837_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00837=true := by decide +kernel
#print axioms leaf00837_sign
theorem leaf00837_log : RationalLog.accepts (546277681/2147483648) (-2939743307/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00837_log
def leaf00837 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (520061509233/1000000000000) (546277681/2147483648) (-2939743307/4294967296) 2 8 ![60,0,4] ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00837
theorem leaf00837_checked : FastNestedCellData.accepts 1 2 4 leaf00837=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (520061509233/1000000000000) (546277681/2147483648) (-2939743307/4294967296) 2 8 ![60,0,4] ![(157/3200),0,(1/8)] ![(3/3200),1,(1/8)] 2398360390852072002576168517632000000000000 927383141323835626409958422742284718047232 1783218186424840352822517039104000000000000 raw00837 affine00837
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00837_raw leaf00837_rectangular
    leaf00837_transform leaf00837_sign leaf00837_log
#print axioms leaf00837_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
