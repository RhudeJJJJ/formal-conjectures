/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00439 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 603727425438959236854841344000000000000 671474149665491077284621912053190230016 80143471448856416230681083904000000000000))
theorem leaf00439_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 603727425438959236854841344000000000000 671474149665491077284621912053190230016 80143471448856416230681083904000000000000 raw00439=true := by decide +kernel
#print axioms leaf00439_raw
theorem leaf00439_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00439=true := by decide +kernel
#print axioms leaf00439_rectangular
def affine00439 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00439 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00439_transform : affine00439=(NestedInteger.clearedAll 3 raw00439 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00439_transform
theorem leaf00439_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00439=true := by decide +kernel
#print axioms leaf00439_sign
theorem leaf00439_log : RationalLog.accepts (4737232711/4294967296) (210473171/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00439_log
def leaf00439 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (523650069/62500000000) (4737232711/4294967296) (210473171/4294967296) 0 8 ![52,0,4] ![(17/64),0,(1/2)] ![(1/64),1,(1/4)] affine00439
theorem leaf00439_checked : FastNestedCellData.accepts 1 0 4 leaf00439=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (523650069/62500000000) (4737232711/4294967296) (210473171/4294967296) 0 8 ![52,0,4] ![(17/64),0,(1/2)] ![(1/64),1,(1/4)] 603727425438959236854841344000000000000 671474149665491077284621912053190230016 80143471448856416230681083904000000000000 raw00439 affine00439
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00439_raw leaf00439_rectangular
    leaf00439_transform leaf00439_sign leaf00439_log
#print axioms leaf00439_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
