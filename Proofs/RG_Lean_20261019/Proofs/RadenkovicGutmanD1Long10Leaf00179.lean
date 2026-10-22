/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00179 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1678650108854688015699673088000000000000 1365156345304919156113389876158341840896 14650146747287197898325884928000000000000))
theorem leaf00179_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1678650108854688015699673088000000000000 1365156345304919156113389876158341840896 14650146747287197898325884928000000000000 raw00179=true := by decide +kernel
#print axioms leaf00179_raw
theorem leaf00179_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00179=true := by decide +kernel
#print axioms leaf00179_rectangular
def affine00179 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00179 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00179_transform : affine00179=(NestedInteger.clearedAll 3 raw00179 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00179_transform
theorem leaf00179_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00179=true := by decide +kernel
#print axioms leaf00179_sign
theorem leaf00179_log : RationalLog.accepts (99847893/134217728) (-317629341/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00179_log
def leaf00179 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (93183800057/1000000000000) (99847893/134217728) (-317629341/2147483648) 1 8 ![52,0,4] ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00179
theorem leaf00179_checked : FastNestedCellData.accepts 1 0 4 leaf00179=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (93183800057/1000000000000) (99847893/134217728) (-317629341/2147483648) 1 8 ![52,0,4] ![(41/1600),0,(1/2)] ![(3/3200),1,(1/2)] 1678650108854688015699673088000000000000 1365156345304919156113389876158341840896 14650146747287197898325884928000000000000 raw00179 affine00179
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00179_raw leaf00179_rectangular
    leaf00179_transform leaf00179_sign leaf00179_log
#print axioms leaf00179_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
