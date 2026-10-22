/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00829 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 618272074167940484967484620800000000000 448295763989082814252613471712760037376 2729660571958001340372536524800000000000))
theorem leaf00829_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 618272074167940484967484620800000000000 448295763989082814252613471712760037376 2729660571958001340372536524800000000000 raw00829=true := by decide +kernel
#print axioms leaf00829_raw
theorem leaf00829_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00829=true := by decide +kernel
#print axioms leaf00829_rectangular
def affine00829 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00829 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00829_transform : affine00829=(NestedInteger.clearedAll 3 raw00829 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00829_transform
theorem leaf00829_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00829=true := by decide +kernel
#print axioms leaf00829_sign
theorem leaf00829_log : RationalLog.accepts (2674887901/4294967296) (-1016911857/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00829_log
def leaf00829 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16423132187/100000000000) (2674887901/4294967296) (-1016911857/4294967296) 1 8 ![60,0,4] ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00829
theorem leaf00829_checked : FastNestedCellData.accepts 1 2 4 leaf00829=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16423132187/100000000000) (2674887901/4294967296) (-1016911857/4294967296) 1 8 ![60,0,4] ![(151/3200),0,(1/2)] ![(3/3200),1,(1/2)] 618272074167940484967484620800000000000 448295763989082814252613471712760037376 2729660571958001340372536524800000000000 raw00829 affine00829
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00829_raw leaf00829_rectangular
    leaf00829_transform leaf00829_sign leaf00829_log
#print axioms leaf00829_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
