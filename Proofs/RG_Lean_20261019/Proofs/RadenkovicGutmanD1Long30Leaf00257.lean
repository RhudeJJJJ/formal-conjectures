/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00257 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15817198089251457609231027404800000000000 13003979124856819974562485584691122405376 151658386967478092953403208499200000000000))
theorem leaf00257_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15817198089251457609231027404800000000000 13003979124856819974562485584691122405376 151658386967478092953403208499200000000000 raw00257=true := by decide +kernel
#print axioms leaf00257_raw
theorem leaf00257_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00257=true := by decide +kernel
#print axioms leaf00257_rectangular
def affine00257 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00257 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00257_transform : affine00257=(NestedInteger.clearedAll 3 raw00257 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00257_transform
theorem leaf00257_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00257=true := by decide +kernel
#print axioms leaf00257_sign
theorem leaf00257_log : RationalLog.accepts (1626105267/2147483648) (-298617295/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00257_log
def leaf00257 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17149040531/200000000000) (1626105267/2147483648) (-298617295/2147483648) 1 8 ![60,0,4] ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)] affine00257
theorem leaf00257_checked : FastNestedCellData.accepts 1 2 4 leaf00257=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17149040531/200000000000) (1626105267/2147483648) (-298617295/2147483648) 1 8 ![60,0,4] ![(7/1280),0,(1/8)] ![(1/6400),1,(1/8)] 15817198089251457609231027404800000000000 13003979124856819974562485584691122405376 151658386967478092953403208499200000000000 raw00257 affine00257
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00257_raw leaf00257_rectangular
    leaf00257_transform leaf00257_sign leaf00257_log
#print axioms leaf00257_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
