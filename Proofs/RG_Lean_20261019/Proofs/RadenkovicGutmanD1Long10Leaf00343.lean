/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00343 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2292435230596468986662864551936000000000000 1371978219558030639577913098795664615145472 2760005032323819910468319838208000000000000))
theorem leaf00343_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2292435230596468986662864551936000000000000 1371978219558030639577913098795664615145472 2760005032323819910468319838208000000000000 raw00343=true := by decide +kernel
#print axioms leaf00343_raw
theorem leaf00343_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00343=true := by decide +kernel
#print axioms leaf00343_rectangular
def affine00343 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00343 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00343_transform : affine00343=(NestedInteger.clearedAll 3 raw00343 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00343_transform
theorem leaf00343_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00343=true := by decide +kernel
#print axioms leaf00343_sign
theorem leaf00343_log : RationalLog.accepts (858482269/2147483648) (-984498895/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00343_log
def leaf00343 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (497092651459/1000000000000) (858482269/2147483648) (-984498895/2147483648) 2 8 ![52,0,4] ![(23/160),0,(1/4)] ![(1/160),1,(1/4)] affine00343
theorem leaf00343_checked : FastNestedCellData.accepts 1 0 4 leaf00343=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (497092651459/1000000000000) (858482269/2147483648) (-984498895/2147483648) 2 8 ![52,0,4] ![(23/160),0,(1/4)] ![(1/160),1,(1/4)] 2292435230596468986662864551936000000000000 1371978219558030639577913098795664615145472 2760005032323819910468319838208000000000000 raw00343 affine00343
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00343_raw leaf00343_rectangular
    leaf00343_transform leaf00343_sign leaf00343_log
#print axioms leaf00343_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
