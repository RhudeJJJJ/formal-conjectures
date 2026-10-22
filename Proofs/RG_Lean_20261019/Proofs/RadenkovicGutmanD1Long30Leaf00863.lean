/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00863 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 64113157750501884840267638374400000000000 34600230228381858636979090618032762912768 99552356225878260476831544115200000000000))
theorem leaf00863_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 64113157750501884840267638374400000000000 34600230228381858636979090618032762912768 99552356225878260476831544115200000000000 raw00863=true := by decide +kernel
#print axioms leaf00863_raw
theorem leaf00863_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00863=true := by decide +kernel
#print axioms leaf00863_rectangular
def affine00863 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00863 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00863_transform : affine00863=(NestedInteger.clearedAll 3 raw00863 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00863_transform
theorem leaf00863_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00863=true := by decide +kernel
#print axioms leaf00863_sign
theorem leaf00863_log : RationalLog.accepts (1720062293/4294967296) (-982563391/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00863_log
def leaf00863 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34755812459/100000000000) (1720062293/4294967296) (-982563391/2147483648) 2 8 ![60,0,4] ![(9/160),0,(1/4)] ![(1/640),1,(1/4)] affine00863
theorem leaf00863_checked : FastNestedCellData.accepts 1 2 4 leaf00863=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34755812459/100000000000) (1720062293/4294967296) (-982563391/2147483648) 2 8 ![60,0,4] ![(9/160),0,(1/4)] ![(1/640),1,(1/4)] 64113157750501884840267638374400000000000 34600230228381858636979090618032762912768 99552356225878260476831544115200000000000 raw00863 affine00863
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00863_raw leaf00863_rectangular
    leaf00863_transform leaf00863_sign leaf00863_log
#print axioms leaf00863_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
