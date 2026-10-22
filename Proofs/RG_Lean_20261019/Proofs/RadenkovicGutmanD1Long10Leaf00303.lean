/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00303 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 816781663416506124464121970688000000000000 141474952970682631323095383239081804693504 199697817603879006925706231808000000000000))
theorem leaf00303_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 816781663416506124464121970688000000000000 141474952970682631323095383239081804693504 199697817603879006925706231808000000000000 raw00303=true := by decide +kernel
#print axioms leaf00303_raw
theorem leaf00303_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00303=true := by decide +kernel
#print axioms leaf00303_rectangular
def affine00303 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00303 (IntegerComputedClassCell.leftNumerator ![(27/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/320),0,0] ![(1/320),1,(1/4)]))
theorem leaf00303_transform : affine00303=(NestedInteger.clearedAll 3 raw00303 (IntegerComputedClassCell.leftNumerator ![(27/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/320),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00303_transform
theorem leaf00303_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00303=true := by decide +kernel
#print axioms leaf00303_sign
theorem leaf00303_log : RationalLog.accepts (217722043/2147483648) (-153600975/134217728) 4 8=true := by decide +kernel
#print axioms leaf00303_log
def leaf00303 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (354222581569/500000000000) (217722043/2147483648) (-153600975/134217728) 4 8 ![52,0,4] ![(27/320),0,0] ![(1/320),1,(1/4)] affine00303
theorem leaf00303_checked : FastNestedCellData.accepts 1 0 4 leaf00303=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (354222581569/500000000000) (217722043/2147483648) (-153600975/134217728) 4 8 ![52,0,4] ![(27/320),0,0] ![(1/320),1,(1/4)] 816781663416506124464121970688000000000000 141474952970682631323095383239081804693504 199697817603879006925706231808000000000000 raw00303 affine00303
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00303_raw leaf00303_rectangular
    leaf00303_transform leaf00303_sign leaf00303_log
#print axioms leaf00303_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
