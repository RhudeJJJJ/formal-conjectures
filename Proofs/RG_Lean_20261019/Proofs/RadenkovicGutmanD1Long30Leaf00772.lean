/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00772 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 103903263100135631398680867635200000000000 43192963866215454813650061548563300614144 95854731416998763924337721344000000000000))
theorem leaf00772_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 103903263100135631398680867635200000000000 43192963866215454813650061548563300614144 95854731416998763924337721344000000000000 raw00772=true := by decide +kernel
#print axioms leaf00772_raw
theorem leaf00772_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00772=true := by decide +kernel
#print axioms leaf00772_rectangular
def affine00772 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00772 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00772_transform : affine00772=(NestedInteger.clearedAll 3 raw00772 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00772_transform
theorem leaf00772_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00772=true := by decide +kernel
#print axioms leaf00772_sign
theorem leaf00772_log : RationalLog.accepts (615408435/2147483648) (-2683851841/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00772_log
def leaf00772 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (225304287163/500000000000) (615408435/2147483648) (-2683851841/4294967296) 2 8 ![60,0,4] ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)] affine00772
theorem leaf00772_checked : FastNestedCellData.accepts 1 2 4 leaf00772=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (225304287163/500000000000) (615408435/2147483648) (-2683851841/4294967296) 2 8 ![60,0,4] ![(59/1600),0,(1/8)] ![(3/3200),1,(1/8)] 103903263100135631398680867635200000000000 43192963866215454813650061548563300614144 95854731416998763924337721344000000000000 raw00772 affine00772
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00772_raw leaf00772_rectangular
    leaf00772_transform leaf00772_sign leaf00772_log
#print axioms leaf00772_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
