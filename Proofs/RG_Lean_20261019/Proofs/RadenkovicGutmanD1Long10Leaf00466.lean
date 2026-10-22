/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00466 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 32843680361169989941256519680000000000 33805150765787076556482744602954039296 30378810544601286006448398008320000000000))
theorem leaf00466_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 32843680361169989941256519680000000000 33805150765787076556482744602954039296 30378810544601286006448398008320000000000 raw00466=true := by decide +kernel
#print axioms leaf00466_raw
theorem leaf00466_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00466=true := by decide +kernel
#print axioms leaf00466_rectangular
def affine00466 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00466 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00466_transform : affine00466=(NestedInteger.clearedAll 3 raw00466 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00466_transform
theorem leaf00466_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00466=true := by decide +kernel
#print axioms leaf00466_sign
theorem leaf00466_log : RationalLog.accepts (4415784929/4294967296) (29787385/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00466_log
def leaf00466 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (44511487/40000000000) (4415784929/4294967296) (29787385/2147483648) 0 8 ![52,0,4] ![(1/8),0,(1/2)] ![(1/64),1,(1/4)] affine00466
theorem leaf00466_checked : FastNestedCellData.accepts 1 0 4 leaf00466=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (44511487/40000000000) (4415784929/4294967296) (29787385/2147483648) 0 8 ![52,0,4] ![(1/8),0,(1/2)] ![(1/64),1,(1/4)] 32843680361169989941256519680000000000 33805150765787076556482744602954039296 30378810544601286006448398008320000000000 raw00466 affine00466
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00466_raw leaf00466_rectangular
    leaf00466_transform leaf00466_sign leaf00466_log
#print axioms leaf00466_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
