/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00444 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 8934287281304546132407353344000000000 9749112817359765766971083389789011968 1610330032381029204864700252160000000000))
theorem leaf00444_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 8934287281304546132407353344000000000 9749112817359765766971083389789011968 1610330032381029204864700252160000000000 raw00444=true := by decide +kernel
#print axioms leaf00444_raw
theorem leaf00444_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00444=true := by decide +kernel
#print axioms leaf00444_rectangular
def affine00444 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00444 (IntegerComputedClassCell.leftNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf00444_transform : affine00444=(NestedInteger.clearedAll 3 raw00444 (IntegerComputedClassCell.leftNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00444_transform
theorem leaf00444_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00444=true := by decide +kernel
#print axioms leaf00444_sign
theorem leaf00444_log : RationalLog.accepts (4658474315/4294967296) (43617569/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00444_log
def leaf00444 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (121082171/20000000000) (4658474315/4294967296) (43617569/1073741824) 0 8 ![52,0,4] ![(15/64),0,0] ![(1/64),1,(1/2)] affine00444
theorem leaf00444_checked : FastNestedCellData.accepts 1 0 4 leaf00444=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (121082171/20000000000) (4658474315/4294967296) (43617569/1073741824) 0 8 ![52,0,4] ![(15/64),0,0] ![(1/64),1,(1/2)] 8934287281304546132407353344000000000 9749112817359765766971083389789011968 1610330032381029204864700252160000000000 raw00444 affine00444
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00444_raw leaf00444_rectangular
    leaf00444_transform leaf00444_sign leaf00444_log
#print axioms leaf00444_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
