/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00288 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 50529064644520851475324207104000000000000 5945236645731766129999706643951840657408 8478277832597990415817244672000000000000))
theorem leaf00288_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 50529064644520851475324207104000000000000 5945236645731766129999706643951840657408 8478277832597990415817244672000000000000 raw00288=true := by decide +kernel
#print axioms leaf00288_raw
theorem leaf00288_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00288=true := by decide +kernel
#print axioms leaf00288_rectangular
def affine00288 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00288 (IntegerComputedClassCell.leftNumerator ![(11/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/160),0,0] ![(1/320),1,(1/4)]))
theorem leaf00288_transform : affine00288=(NestedInteger.clearedAll 3 raw00288 (IntegerComputedClassCell.leftNumerator ![(11/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/160),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00288_transform
theorem leaf00288_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00288=true := by decide +kernel
#print axioms leaf00288_sign
theorem leaf00288_log : RationalLog.accepts (297046403/4294967296) (-717074565/536870912) 4 8=true := by decide +kernel
#print axioms leaf00288_log
def leaf00288 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (43826977329/62500000000) (297046403/4294967296) (-717074565/536870912) 4 8 ![52,0,4] ![(11/160),0,0] ![(1/320),1,(1/4)] affine00288
theorem leaf00288_checked : FastNestedCellData.accepts 1 0 4 leaf00288=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (43826977329/62500000000) (297046403/4294967296) (-717074565/536870912) 4 8 ![52,0,4] ![(11/160),0,0] ![(1/320),1,(1/4)] 50529064644520851475324207104000000000000 5945236645731766129999706643951840657408 8478277832597990415817244672000000000000 raw00288 affine00288
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00288_raw leaf00288_rectangular
    leaf00288_transform leaf00288_sign leaf00288_log
#print axioms leaf00288_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
