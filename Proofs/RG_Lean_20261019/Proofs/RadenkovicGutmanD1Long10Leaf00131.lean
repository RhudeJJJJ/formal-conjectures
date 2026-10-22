/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00131 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1036929668314784143671033856000000000000 907129692187598291202758568195609591808 15759406133502885210527629312000000000000))
theorem leaf00131_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1036929668314784143671033856000000000000 907129692187598291202758568195609591808 15759406133502885210527629312000000000000 raw00131=true := by decide +kernel
#print axioms leaf00131_raw
theorem leaf00131_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00131=true := by decide +kernel
#print axioms leaf00131_rectangular
def affine00131 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00131 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00131_transform : affine00131=(NestedInteger.clearedAll 3 raw00131 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00131_transform
theorem leaf00131_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00131=true := by decide +kernel
#print axioms leaf00131_sign
theorem leaf00131_log : RationalLog.accepts (222051887/268435456) (-203688217/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00131_log
def leaf00131 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (28780579817/500000000000) (222051887/268435456) (-203688217/2147483648) 1 8 ![52,0,4] ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)] affine00131
theorem leaf00131_checked : FastNestedCellData.accepts 1 0 4 leaf00131=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (28780579817/500000000000) (222051887/268435456) (-203688217/2147483648) 1 8 ![52,0,4] ![(1/64),0,(1/2)] ![(1/1600),1,(1/2)] 1036929668314784143671033856000000000000 907129692187598291202758568195609591808 15759406133502885210527629312000000000000 raw00131 affine00131
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00131_raw leaf00131_rectangular
    leaf00131_transform leaf00131_sign leaf00131_log
#print axioms leaf00131_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
