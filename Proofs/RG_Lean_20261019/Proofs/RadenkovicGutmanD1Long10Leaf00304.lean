/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00304 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 508461388588363519086146093056000000000000 260465007606880439891902079355279401549824 590596877574650334072750997504000000000000))
theorem leaf00304_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 508461388588363519086146093056000000000000 260465007606880439891902079355279401549824 590596877574650334072750997504000000000000 raw00304=true := by decide +kernel
#print axioms leaf00304_raw
theorem leaf00304_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00304=true := by decide +kernel
#print axioms leaf00304_rectangular
def affine00304 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00304 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00304_transform : affine00304=(NestedInteger.clearedAll 3 raw00304 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00304_transform
theorem leaf00304_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00304=true := by decide +kernel
#print axioms leaf00304_sign
theorem leaf00304_log : RationalLog.accepts (763398457/2147483648) (-2221082107/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00304_log
def leaf00304 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (220509976853/500000000000) (763398457/2147483648) (-2221082107/4294967296) 2 8 ![52,0,4] ![(27/320),0,(1/4)] ![(1/320),1,(1/4)] affine00304
theorem leaf00304_checked : FastNestedCellData.accepts 1 0 4 leaf00304=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (220509976853/500000000000) (763398457/2147483648) (-2221082107/4294967296) 2 8 ![52,0,4] ![(27/320),0,(1/4)] ![(1/320),1,(1/4)] 508461388588363519086146093056000000000000 260465007606880439891902079355279401549824 590596877574650334072750997504000000000000 raw00304 affine00304
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00304_raw leaf00304_rectangular
    leaf00304_transform leaf00304_sign leaf00304_log
#print axioms leaf00304_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
