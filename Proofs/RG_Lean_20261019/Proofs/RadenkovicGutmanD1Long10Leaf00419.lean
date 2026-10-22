/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00419 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 47674442717408471186740871168000000000000 60574885539634285385757437281851370635264 1464895742813604042356973109248000000000000))
theorem leaf00419_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 47674442717408471186740871168000000000000 60574885539634285385757437281851370635264 1464895742813604042356973109248000000000000 raw00419=true := by decide +kernel
#print axioms leaf00419_raw
theorem leaf00419_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00419=true := by decide +kernel
#print axioms leaf00419_rectangular
def affine00419 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00419 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00419_transform : affine00419=(NestedInteger.clearedAll 3 raw00419 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00419_transform
theorem leaf00419_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00419=true := by decide +kernel
#print axioms leaf00419_sign
theorem leaf00419_log : RationalLog.accepts (1310115889/1073741824) (213638135/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00419_log
def leaf00419 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (41350987493/1000000000000) (1310115889/1073741824) (213638135/2147483648) 0 8 ![52,0,4] ![(1/2),0,(3/4)] ![(1/16),1,(1/4)] affine00419
theorem leaf00419_checked : FastNestedCellData.accepts 1 0 4 leaf00419=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (41350987493/1000000000000) (1310115889/1073741824) (213638135/2147483648) 0 8 ![52,0,4] ![(1/2),0,(3/4)] ![(1/16),1,(1/4)] 47674442717408471186740871168000000000000 60574885539634285385757437281851370635264 1464895742813604042356973109248000000000000 raw00419 affine00419
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00419_raw leaf00419_rectangular
    leaf00419_transform leaf00419_sign leaf00419_log
#print axioms leaf00419_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
