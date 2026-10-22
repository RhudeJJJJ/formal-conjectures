/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00223 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5039637165210580126472494645248000000000000 2946124115048778267798014859408051969982464 10783791725096938703689338585088000000000000))
theorem leaf00223_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5039637165210580126472494645248000000000000 2946124115048778267798014859408051969982464 10783791725096938703689338585088000000000000 raw00223=true := by decide +kernel
#print axioms leaf00223_raw
theorem leaf00223_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00223=true := by decide +kernel
#print axioms leaf00223_rectangular
def affine00223 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00223 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00223_transform : affine00223=(NestedInteger.clearedAll 3 raw00223 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00223_transform
theorem leaf00223_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00223=true := by decide +kernel
#print axioms leaf00223_sign
theorem leaf00223_log : RationalLog.accepts (1972037851/4294967296) (-1671550857/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00223_log
def leaf00223 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (273199278153/1000000000000) (1972037851/4294967296) (-1671550857/4294967296) 2 8 ![52,0,4] ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00223
theorem leaf00223_checked : FastNestedCellData.accepts 1 0 4 leaf00223=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (273199278153/1000000000000) (1972037851/4294967296) (-1671550857/4294967296) 2 8 ![52,0,4] ![(127/3200),0,(1/4)] ![(3/3200),1,(1/4)] 5039637165210580126472494645248000000000000 2946124115048778267798014859408051969982464 10783791725096938703689338585088000000000000 raw00223 affine00223
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00223_raw leaf00223_rectangular
    leaf00223_transform leaf00223_sign leaf00223_log
#print axioms leaf00223_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
