/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00801 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 51228665971652614916986109952000000000 12830183519898367846396385067156897792 18479896543958834140984377344000000000))
theorem leaf00801_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 51228665971652614916986109952000000000 12830183519898367846396385067156897792 18479896543958834140984377344000000000 raw00801=true := by decide +kernel
#print axioms leaf00801_raw
theorem leaf00801_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00801=true := by decide +kernel
#print axioms leaf00801_rectangular
def affine00801 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00801 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00801_transform : affine00801=(NestedInteger.clearedAll 3 raw00801 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00801_transform
theorem leaf00801_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00801=true := by decide +kernel
#print axioms leaf00801_sign
theorem leaf00801_log : RationalLog.accepts (317442481/2147483648) (-2052731783/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00801_log
def leaf00801 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2777111547/4000000000) (317442481/2147483648) (-2052731783/2147483648) 3 8 ![60,0,4] ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)] affine00801
theorem leaf00801_checked : FastNestedCellData.accepts 1 2 4 leaf00801=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2777111547/4000000000) (317442481/2147483648) (-2052731783/2147483648) 3 8 ![60,0,4] ![(17/400),0,(1/16)] ![(3/3200),1,(1/16)] 51228665971652614916986109952000000000 12830183519898367846396385067156897792 18479896543958834140984377344000000000 raw00801 affine00801
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00801_raw leaf00801_rectangular
    leaf00801_transform leaf00801_sign leaf00801_log
#print axioms leaf00801_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
