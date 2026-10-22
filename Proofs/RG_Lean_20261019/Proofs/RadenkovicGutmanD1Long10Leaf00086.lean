/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00086 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 616972878708139068111787655168000000000000 569883630576128373528942634815589516836864 17038832415204508539958138503168000000000000))
theorem leaf00086_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 616972878708139068111787655168000000000000 569883630576128373528942634815589516836864 17038832415204508539958138503168000000000000 raw00086=true := by decide +kernel
#print axioms leaf00086_raw
theorem leaf00086_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00086=true := by decide +kernel
#print axioms leaf00086_rectangular
def affine00086 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00086 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00086_transform : affine00086=(NestedInteger.clearedAll 3 raw00086 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00086_transform
theorem leaf00086_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00086=true := by decide +kernel
#print axioms leaf00086_sign
theorem leaf00086_log : RationalLog.accepts (3838770171/4294967296) (-241145041/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00086_log
def leaf00086 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (33446166773/1000000000000) (3838770171/4294967296) (-241145041/4294967296) 1 8 ![52,0,4] ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00086
theorem leaf00086_checked : FastNestedCellData.accepts 1 0 4 leaf00086=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (33446166773/1000000000000) (3838770171/4294967296) (-241145041/4294967296) 1 8 ![52,0,4] ![(29/3200),0,(1/2)] ![(1/3200),1,(1/2)] 616972878708139068111787655168000000000000 569883630576128373528942634815589516836864 17038832415204508539958138503168000000000000 raw00086 affine00086
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00086_raw leaf00086_rectangular
    leaf00086_transform leaf00086_sign leaf00086_log
#print axioms leaf00086_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
