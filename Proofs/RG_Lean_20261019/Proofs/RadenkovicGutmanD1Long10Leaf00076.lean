/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00076 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4394520489833344308084736000000000000 3800043665613432486063042246645645312 60849483166170219427135488000000000000))
theorem leaf00076_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4394520489833344308084736000000000000 3800043665613432486063042246645645312 60849483166170219427135488000000000000 raw00076=true := by decide +kernel
#print axioms leaf00076_raw
theorem leaf00076_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00076=true := by decide +kernel
#print axioms leaf00076_rectangular
def affine00076 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00076 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00076_transform : affine00076=(NestedInteger.clearedAll 3 raw00076 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00076_transform
theorem leaf00076_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00076=true := by decide +kernel
#print axioms leaf00076_sign
theorem leaf00076_log : RationalLog.accepts (873913617/1073741824) (-27638563/268435456) 1 8=true := by decide +kernel
#print axioms leaf00076_log
def leaf00076 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (487889783/7812500000) (873913617/1073741824) (-27638563/268435456) 1 8 ![52,0,4] ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00076
theorem leaf00076_checked : FastNestedCellData.accepts 1 0 4 leaf00076=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (487889783/7812500000) (873913617/1073741824) (-27638563/268435456) 1 8 ![52,0,4] ![(13/1600),0,(1/4)] ![(1/3200),1,(1/4)] 4394520489833344308084736000000000000 3800043665613432486063042246645645312 60849483166170219427135488000000000000 raw00076 affine00076
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00076_raw leaf00076_rectangular
    leaf00076_transform leaf00076_sign leaf00076_log
#print axioms leaf00076_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
