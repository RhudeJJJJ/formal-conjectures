/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00199 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1060524650747619586661209341952000000000000 661916796451245918738936045548517189484544 2878341803186331732334333657088000000000000))
theorem leaf00199_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1060524650747619586661209341952000000000000 661916796451245918738936045548517189484544 2878341803186331732334333657088000000000000 raw00199=true := by decide +kernel
#print axioms leaf00199_raw
theorem leaf00199_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00199=true := by decide +kernel
#print axioms leaf00199_rectangular
def affine00199 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00199 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00199_transform : affine00199=(NestedInteger.clearedAll 3 raw00199 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00199_transform
theorem leaf00199_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00199=true := by decide +kernel
#print axioms leaf00199_sign
theorem leaf00199_log : RationalLog.accepts (1089732437/2147483648) (-728388423/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00199_log
def leaf00199 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (229964626063/1000000000000) (1089732437/2147483648) (-728388423/2147483648) 1 8 ![52,0,4] ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00199
theorem leaf00199_checked : FastNestedCellData.accepts 1 0 4 leaf00199=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (229964626063/1000000000000) (1089732437/2147483648) (-728388423/2147483648) 1 8 ![52,0,4] ![(103/3200),0,(1/4)] ![(3/3200),1,(1/4)] 1060524650747619586661209341952000000000000 661916796451245918738936045548517189484544 2878341803186331732334333657088000000000000 raw00199 affine00199
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00199_raw leaf00199_rectangular
    leaf00199_transform leaf00199_sign leaf00199_log
#print axioms leaf00199_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
