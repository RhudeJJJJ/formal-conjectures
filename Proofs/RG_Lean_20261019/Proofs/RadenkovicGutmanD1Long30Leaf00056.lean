/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00056 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16629184695016878361907979878400000000000 14665792903507193350750311506479524347904 271145913335218113027994812416000000000000))
theorem leaf00056_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16629184695016878361907979878400000000000 14665792903507193350750311506479524347904 271145913335218113027994812416000000000000 raw00056=true := by decide +kernel
#print axioms leaf00056_raw
theorem leaf00056_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00056=true := by decide +kernel
#print axioms leaf00056_rectangular
def affine00056 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00056 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00056_transform : affine00056=(NestedInteger.clearedAll 3 raw00056 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00056_transform
theorem leaf00056_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00056=true := by decide +kernel
#print axioms leaf00056_sign
theorem leaf00056_log : RationalLog.accepts (1796749395/2147483648) (-5983347/67108864) 1 8=true := by decide +kernel
#print axioms leaf00056_log
def leaf00056 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (54088194519/1000000000000) (1796749395/2147483648) (-5983347/67108864) 1 8 ![60,0,4] ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00056
theorem leaf00056_checked : FastNestedCellData.accepts 1 2 4 leaf00056=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (54088194519/1000000000000) (1796749395/2147483648) (-5983347/67108864) 1 8 ![60,0,4] ![(27/16000),0,(1/16)] ![(1/16000),1,(1/16)] 16629184695016878361907979878400000000000 14665792903507193350750311506479524347904 271145913335218113027994812416000000000000 raw00056 affine00056
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00056_raw leaf00056_rectangular
    leaf00056_transform leaf00056_sign leaf00056_log
#print axioms leaf00056_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
