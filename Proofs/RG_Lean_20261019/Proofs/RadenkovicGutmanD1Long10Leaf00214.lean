/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00214 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1583497496305702793135412740096000000000000 947037820347240309104487862729245556998144 3677463829450567335949849591808000000000000))
theorem leaf00214_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1583497496305702793135412740096000000000000 947037820347240309104487862729245556998144 3677463829450567335949849591808000000000000 raw00214=true := by decide +kernel
#print axioms leaf00214_raw
theorem leaf00214_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00214=true := by decide +kernel
#print axioms leaf00214_rectangular
def affine00214 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00214 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00214_transform : affine00214=(NestedInteger.clearedAll 3 raw00214 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00214_transform
theorem leaf00214_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00214=true := by decide +kernel
#print axioms leaf00214_sign
theorem leaf00214_log : RationalLog.accepts (2042646783/4294967296) (-798002309/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00214_log
def leaf00214 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (257524713843/1000000000000) (2042646783/4294967296) (-798002309/2147483648) 2 8 ![52,0,4] ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00214
theorem leaf00214_checked : FastNestedCellData.accepts 1 0 4 leaf00214=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (257524713843/1000000000000) (2042646783/4294967296) (-798002309/2147483648) 2 8 ![52,0,4] ![(59/1600),0,(1/4)] ![(3/3200),1,(1/4)] 1583497496305702793135412740096000000000000 947037820347240309104487862729245556998144 3677463829450567335949849591808000000000000 raw00214 affine00214
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00214_raw leaf00214_rectangular
    leaf00214_transform leaf00214_sign leaf00214_log
#print axioms leaf00214_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
