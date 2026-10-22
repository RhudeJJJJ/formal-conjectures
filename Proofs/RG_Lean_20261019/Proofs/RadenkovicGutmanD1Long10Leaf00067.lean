/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00067 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 20453425544391707054758166528000000000 17957346859722450182831295345561960448 323911103345680257073146757120000000000))
theorem leaf00067_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 20453425544391707054758166528000000000 17957346859722450182831295345561960448 323911103345680257073146757120000000000 raw00067=true := by decide +kernel
#print axioms leaf00067_raw
theorem leaf00067_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00067=true := by decide +kernel
#print axioms leaf00067_rectangular
def affine00067 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00067 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00067_transform : affine00067=(NestedInteger.clearedAll 3 raw00067 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00067_transform
theorem leaf00067_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00067=true := by decide +kernel
#print axioms leaf00067_sign
theorem leaf00067_log : RationalLog.accepts (893187835/1073741824) (-197684433/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00067_log
def leaf00067 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2217564841/40000000000) (893187835/1073741824) (-197684433/2147483648) 1 8 ![52,0,4] ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00067
theorem leaf00067_checked : FastNestedCellData.accepts 1 0 4 leaf00067=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2217564841/40000000000) (893187835/1073741824) (-197684433/2147483648) 1 8 ![52,0,4] ![(23/3200),0,(1/4)] ![(1/3200),1,(1/4)] 20453425544391707054758166528000000000 17957346859722450182831295345561960448 323911103345680257073146757120000000000 raw00067 affine00067
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00067_raw leaf00067_rectangular
    leaf00067_transform leaf00067_sign leaf00067_log
#print axioms leaf00067_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
