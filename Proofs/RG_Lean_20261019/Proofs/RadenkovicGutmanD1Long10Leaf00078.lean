/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00078 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3619903149928868589309549084672000000000000 2704718710433190150275199882127252389888 13783035560969413770623320064000000000000))
theorem leaf00078_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3619903149928868589309549084672000000000000 2704718710433190150275199882127252389888 13783035560969413770623320064000000000000 raw00078=true := by decide +kernel
#print axioms leaf00078_raw
theorem leaf00078_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00078=true := by decide +kernel
#print axioms leaf00078_rectangular
def affine00078 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00078 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00078_transform : affine00078=(NestedInteger.clearedAll 3 raw00078 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00078_transform
theorem leaf00078_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00078=true := by decide +kernel
#print axioms leaf00078_sign
theorem leaf00078_log : RationalLog.accepts (2682677/4294967296) (-7922479735/2147483648) 11 8=true := by decide +kernel
#print axioms leaf00078_log
def leaf00078 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (196235342967/1000000000000) (2682677/4294967296) (-7922479735/2147483648) 11 8 ![52,0,4] ![(27/3200),0,0] ![(1/3200),1,(1/4)] affine00078
theorem leaf00078_checked : FastNestedCellData.accepts 1 0 4 leaf00078=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (196235342967/1000000000000) (2682677/4294967296) (-7922479735/2147483648) 11 8 ![52,0,4] ![(27/3200),0,0] ![(1/3200),1,(1/4)] 3619903149928868589309549084672000000000000 2704718710433190150275199882127252389888 13783035560969413770623320064000000000000 raw00078 affine00078
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00078_raw leaf00078_rectangular
    leaf00078_transform leaf00078_sign leaf00078_log
#print axioms leaf00078_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
