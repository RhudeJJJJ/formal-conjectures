/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00467 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 32843680361169989941256519680000000000 33805150765787076556482744602954039296 30378810544601286006448398008320000000000))
theorem leaf00467_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 32843680361169989941256519680000000000 33805150765787076556482744602954039296 30378810544601286006448398008320000000000 raw00467=true := by decide +kernel
#print axioms leaf00467_raw
theorem leaf00467_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00467=true := by decide +kernel
#print axioms leaf00467_rectangular
def affine00467 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00467 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00467_transform : affine00467=(NestedInteger.clearedAll 3 raw00467 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00467_transform
theorem leaf00467_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00467=true := by decide +kernel
#print axioms leaf00467_sign
theorem leaf00467_log : RationalLog.accepts (4415784929/4294967296) (29787385/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00467_log
def leaf00467 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (44511487/40000000000) (4415784929/4294967296) (29787385/2147483648) 0 8 ![52,0,4] ![(1/8),0,(3/4)] ![(1/64),1,(1/4)] affine00467
theorem leaf00467_checked : FastNestedCellData.accepts 1 0 4 leaf00467=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (44511487/40000000000) (4415784929/4294967296) (29787385/2147483648) 0 8 ![52,0,4] ![(1/8),0,(3/4)] ![(1/64),1,(1/4)] 32843680361169989941256519680000000000 33805150765787076556482744602954039296 30378810544601286006448398008320000000000 raw00467 affine00467
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00467_raw leaf00467_rectangular
    leaf00467_transform leaf00467_sign leaf00467_log
#print axioms leaf00467_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
