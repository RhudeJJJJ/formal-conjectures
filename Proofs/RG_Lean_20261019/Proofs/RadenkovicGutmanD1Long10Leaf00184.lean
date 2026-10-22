/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00184 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4820154061898331845759598592000000000000 3158392913000409392826853328161270136832 15738514538103191945925885952000000000000))
theorem leaf00184_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4820154061898331845759598592000000000000 3158392913000409392826853328161270136832 15738514538103191945925885952000000000000 raw00184=true := by decide +kernel
#print axioms leaf00184_raw
theorem leaf00184_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00184=true := by decide +kernel
#print axioms leaf00184_rectangular
def affine00184 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00184 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00184_transform : affine00184=(NestedInteger.clearedAll 3 raw00184 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00184_transform
theorem leaf00184_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00184=true := by decide +kernel
#print axioms leaf00184_sign
theorem leaf00184_log : RationalLog.accepts (1171947363/2147483648) (-162572565/536870912) 1 8=true := by decide +kernel
#print axioms leaf00184_log
def leaf00184 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (25084903227/125000000000) (1171947363/2147483648) (-162572565/536870912) 1 8 ![52,0,4] ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)] affine00184
theorem leaf00184_checked : FastNestedCellData.accepts 1 0 4 leaf00184=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (25084903227/125000000000) (1171947363/2147483648) (-162572565/536870912) 1 8 ![52,0,4] ![(11/400),0,(1/4)] ![(3/3200),1,(1/4)] 4820154061898331845759598592000000000000 3158392913000409392826853328161270136832 15738514538103191945925885952000000000000 raw00184 affine00184
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00184_raw leaf00184_rectangular
    leaf00184_transform leaf00184_sign leaf00184_log
#print axioms leaf00184_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
