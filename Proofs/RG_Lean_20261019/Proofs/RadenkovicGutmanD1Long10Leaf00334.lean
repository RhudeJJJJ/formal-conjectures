/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00334 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1814630425664733756182643290931200000000000 1018781761966913558552446949135053853032448 2071298504000584866219979440128000000000000))
theorem leaf00334_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1814630425664733756182643290931200000000000 1018781761966913558552446949135053853032448 2071298504000584866219979440128000000000000 raw00334=true := by decide +kernel
#print axioms leaf00334_raw
theorem leaf00334_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00334=true := by decide +kernel
#print axioms leaf00334_rectangular
def affine00334 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00334 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00334_transform : affine00334=(NestedInteger.clearedAll 3 raw00334 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00334_transform
theorem leaf00334_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00334=true := by decide +kernel
#print axioms leaf00334_sign
theorem leaf00334_log : RationalLog.accepts (1616314115/4294967296) (-1049363219/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00334_log
def leaf00334 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (491856562441/1000000000000) (1616314115/4294967296) (-1049363219/2147483648) 2 8 ![52,0,4] ![(1/8),0,(1/4)] ![(1/160),1,(1/4)] affine00334
theorem leaf00334_checked : FastNestedCellData.accepts 1 0 4 leaf00334=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (491856562441/1000000000000) (1616314115/4294967296) (-1049363219/2147483648) 2 8 ![52,0,4] ![(1/8),0,(1/4)] ![(1/160),1,(1/4)] 1814630425664733756182643290931200000000000 1018781761966913558552446949135053853032448 2071298504000584866219979440128000000000000 raw00334 affine00334
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00334_raw leaf00334_rectangular
    leaf00334_transform leaf00334_sign leaf00334_log
#print axioms leaf00334_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
