/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00033 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 6216845058865846985577988096000000000000 387101029108087803411595613083533312 4486772397094838093217792000000000000))
theorem leaf00033_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 6216845058865846985577988096000000000000 387101029108087803411595613083533312 4486772397094838093217792000000000000 raw00033=true := by decide +kernel
#print axioms leaf00033_raw
theorem leaf00033_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00033=true := by decide +kernel
#print axioms leaf00033_rectangular
def affine00033 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00033 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/2000),0,0] ![(3/8000),1,(1/4)]))
theorem leaf00033_transform : affine00033=(NestedInteger.clearedAll 3 raw00033 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/2000),0,0] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00033_transform
theorem leaf00033_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00033=true := by decide +kernel
#print axioms leaf00033_sign
theorem leaf00033_log : RationalLog.accepts (15387/268435456) (-20974135691/4294967296) 15 8=true := by decide +kernel
#print axioms leaf00033_log
def leaf00033 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (86276056561/1000000000000) (15387/268435456) (-20974135691/4294967296) 15 8 ![52,0,4] ![(7/2000),0,0] ![(3/8000),1,(1/4)] affine00033
theorem leaf00033_checked : FastNestedCellData.accepts 1 0 4 leaf00033=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (86276056561/1000000000000) (15387/268435456) (-20974135691/4294967296) 15 8 ![52,0,4] ![(7/2000),0,0] ![(3/8000),1,(1/4)] 6216845058865846985577988096000000000000 387101029108087803411595613083533312 4486772397094838093217792000000000000 raw00033 affine00033
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00033_raw leaf00033_rectangular
    leaf00033_transform leaf00033_sign leaf00033_log
#print axioms leaf00033_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
