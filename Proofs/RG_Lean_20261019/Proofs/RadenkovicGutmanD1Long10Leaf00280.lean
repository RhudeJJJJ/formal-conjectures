/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00280 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 252201549631792316119999578112000000000000 130690083065417841923627829441102593654784 341394542635687357667453435904000000000000))
theorem leaf00280_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 252201549631792316119999578112000000000000 130690083065417841923627829441102593654784 341394542635687357667453435904000000000000 raw00280=true := by decide +kernel
#print axioms leaf00280_raw
theorem leaf00280_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00280=true := by decide +kernel
#print axioms leaf00280_rectangular
def affine00280 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00280 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00280_transform : affine00280=(NestedInteger.clearedAll 3 raw00280 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00280_transform
theorem leaf00280_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00280=true := by decide +kernel
#print axioms leaf00280_sign
theorem leaf00280_log : RationalLog.accepts (804750891/2147483648) (-526949159/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00280_log
def leaf00280 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (382812455221/1000000000000) (804750891/2147483648) (-526949159/1073741824) 2 8 ![52,0,4] ![(41/640),0,(1/4)] ![(1/640),1,(1/4)] affine00280
theorem leaf00280_checked : FastNestedCellData.accepts 1 0 4 leaf00280=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (382812455221/1000000000000) (804750891/2147483648) (-526949159/1073741824) 2 8 ![52,0,4] ![(41/640),0,(1/4)] ![(1/640),1,(1/4)] 252201549631792316119999578112000000000000 130690083065417841923627829441102593654784 341394542635687357667453435904000000000000 raw00280 affine00280
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00280_raw leaf00280_rectangular
    leaf00280_transform leaf00280_sign leaf00280_log
#print axioms leaf00280_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
