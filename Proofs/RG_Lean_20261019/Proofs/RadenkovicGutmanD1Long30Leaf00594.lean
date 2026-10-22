/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00594 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 80863372812206904480242860032000000000000 69201265078537872911905441558414906884096 986647277752446555526610812928000000000000))
theorem leaf00594_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 80863372812206904480242860032000000000000 69201265078537872911905441558414906884096 986647277752446555526610812928000000000000 raw00594=true := by decide +kernel
#print axioms leaf00594_raw
theorem leaf00594_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00594=true := by decide +kernel
#print axioms leaf00594_rectangular
def affine00594 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00594 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00594_transform : affine00594=(NestedInteger.clearedAll 3 raw00594 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00594_transform
theorem leaf00594_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00594=true := by decide +kernel
#print axioms leaf00594_sign
theorem leaf00594_log : RationalLog.accepts (1717324417/2147483648) (-240012725/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00594_log
def leaf00594 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (35068897791/500000000000) (1717324417/2147483648) (-240012725/2147483648) 1 8 ![60,0,4] ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00594
theorem leaf00594_checked : FastNestedCellData.accepts 1 2 4 leaf00594=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (35068897791/500000000000) (1717324417/2147483648) (-240012725/2147483648) 1 8 ![60,0,4] ![(61/3200),0,(1/2)] ![(1/3200),1,(1/2)] 80863372812206904480242860032000000000000 69201265078537872911905441558414906884096 986647277752446555526610812928000000000000 raw00594 affine00594
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00594_raw leaf00594_rectangular
    leaf00594_transform leaf00594_sign leaf00594_log
#print axioms leaf00594_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
