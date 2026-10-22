/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00584 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12526671439022209847593072066560000000000 10768468278282908477357111316043882561536 158576186309593160350796087296000000000000))
theorem leaf00584_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12526671439022209847593072066560000000000 10768468278282908477357111316043882561536 158576186309593160350796087296000000000000 raw00584=true := by decide +kernel
#print axioms leaf00584_raw
theorem leaf00584_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00584=true := by decide +kernel
#print axioms leaf00584_rectangular
def affine00584 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00584 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00584_transform : affine00584=(NestedInteger.clearedAll 3 raw00584 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00584_transform
theorem leaf00584_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00584=true := by decide +kernel
#print axioms leaf00584_sign
theorem leaf00584_log : RationalLog.accepts (1728679925/2147483648) (-232936165/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00584_log
def leaf00584 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (67907221941/1000000000000) (1728679925/2147483648) (-232936165/2147483648) 1 8 ![60,0,4] ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00584
theorem leaf00584_checked : FastNestedCellData.accepts 1 2 4 leaf00584=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (67907221941/1000000000000) (1728679925/2147483648) (-232936165/2147483648) 1 8 ![60,0,4] ![(59/3200),0,(1/2)] ![(1/3200),1,(1/2)] 12526671439022209847593072066560000000000 10768468278282908477357111316043882561536 158576186309593160350796087296000000000000 raw00584 affine00584
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00584_raw leaf00584_rectangular
    leaf00584_transform leaf00584_sign leaf00584_log
#print axioms leaf00584_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
