/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00527 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1034445882149341366082177335296000000000000 637038828966572000607964789202222466465792 2839996863476679356351258820608000000000000))
theorem leaf00527_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1034445882149341366082177335296000000000000 637038828966572000607964789202222466465792 2839996863476679356351258820608000000000000 raw00527=true := by decide +kernel
#print axioms leaf00527_raw
theorem leaf00527_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00527=true := by decide +kernel
#print axioms leaf00527_rectangular
def affine00527 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00527 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00527_transform : affine00527=(NestedInteger.clearedAll 3 raw00527 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00527_transform
theorem leaf00527_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00527=true := by decide +kernel
#print axioms leaf00527_sign
theorem leaf00527_log : RationalLog.accepts (1080181429/2147483648) (-184460191/536870912) 1 8=true := by decide +kernel
#print axioms leaf00527_log
def leaf00527 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (224309694549/1000000000000) (1080181429/2147483648) (-184460191/536870912) 1 8 ![60,0,4] ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)] affine00527
theorem leaf00527_checked : FastNestedCellData.accepts 1 2 4 leaf00527=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (224309694549/1000000000000) (1080181429/2147483648) (-184460191/536870912) 1 8 ![60,0,4] ![(3/200),0,(1/8)] ![(1/3200),1,(1/8)] 1034445882149341366082177335296000000000000 637038828966572000607964789202222466465792 2839996863476679356351258820608000000000000 raw00527 affine00527
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00527_raw leaf00527_rectangular
    leaf00527_transform leaf00527_sign leaf00527_log
#print axioms leaf00527_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
