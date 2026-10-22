/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00060 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 715674577842975229854846287872000000000000 264953004008570601485358189056177995776 1707312376260975749687672832000000000000))
theorem leaf00060_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 715674577842975229854846287872000000000000 264953004008570601485358189056177995776 1707312376260975749687672832000000000000 raw00060=true := by decide +kernel
#print axioms leaf00060_raw
theorem leaf00060_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00060=true := by decide +kernel
#print axioms leaf00060_rectangular
def affine00060 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00060 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00060_transform : affine00060=(NestedInteger.clearedAll 3 raw00060 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00060_transform
theorem leaf00060_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00060=true := by decide +kernel
#print axioms leaf00060_sign
theorem leaf00060_log : RationalLog.accepts (1376451/4294967296) (-8638994897/2147483648) 12 8=true := by decide +kernel
#print axioms leaf00060_log
def leaf00060 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (77593593209/500000000000) (1376451/4294967296) (-8638994897/2147483648) 12 8 ![52,0,4] ![(21/3200),0,0] ![(1/3200),1,(1/4)] affine00060
theorem leaf00060_checked : FastNestedCellData.accepts 1 0 4 leaf00060=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (77593593209/500000000000) (1376451/4294967296) (-8638994897/2147483648) 12 8 ![52,0,4] ![(21/3200),0,0] ![(1/3200),1,(1/4)] 715674577842975229854846287872000000000000 264953004008570601485358189056177995776 1707312376260975749687672832000000000000 raw00060 affine00060
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00060_raw leaf00060_rectangular
    leaf00060_transform leaf00060_sign leaf00060_log
#print axioms leaf00060_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
