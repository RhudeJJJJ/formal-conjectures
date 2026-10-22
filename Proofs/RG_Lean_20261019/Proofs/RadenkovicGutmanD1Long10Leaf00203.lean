/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00203 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2187377152642356718637470973952000000000000 1699137270984618377129429471397254352863232 14329284890852703345784291065856000000000000))
theorem leaf00203_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2187377152642356718637470973952000000000000 1699137270984618377129429471397254352863232 14329284890852703345784291065856000000000000 raw00203=true := by decide +kernel
#print axioms leaf00203_raw
theorem leaf00203_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00203=true := by decide +kernel
#print axioms leaf00203_rectangular
def affine00203 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00203 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00203_transform : affine00203=(NestedInteger.clearedAll 3 raw00203 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00203_transform
theorem leaf00203_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00203=true := by decide +kernel
#print axioms leaf00203_sign
theorem leaf00203_log : RationalLog.accepts (2982623263/4294967296) (-391530029/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00203_log
def leaf00203 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (118577953047/1000000000000) (2982623263/4294967296) (-391530029/2147483648) 1 8 ![52,0,4] ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00203
theorem leaf00203_checked : FastNestedCellData.accepts 1 0 4 leaf00203=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (118577953047/1000000000000) (2982623263/4294967296) (-391530029/2147483648) 1 8 ![52,0,4] ![(53/1600),0,(1/2)] ![(3/3200),1,(1/2)] 2187377152642356718637470973952000000000000 1699137270984618377129429471397254352863232 14329284890852703345784291065856000000000000 raw00203 affine00203
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00203_raw leaf00203_rectangular
    leaf00203_transform leaf00203_sign leaf00203_log
#print axioms leaf00203_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
