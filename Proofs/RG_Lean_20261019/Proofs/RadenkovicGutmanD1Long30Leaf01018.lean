/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01018 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1658184952758924977537402745651200000000000 1148866672921015335387028584234718777573376 2556150259948628221113386663936000000000000))
theorem leaf01018_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1658184952758924977537402745651200000000000 1148866672921015335387028584234718777573376 2556150259948628221113386663936000000000000 raw01018=true := by decide +kernel
#print axioms leaf01018_raw
theorem leaf01018_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01018=true := by decide +kernel
#print axioms leaf01018_rectangular
def affine01018 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01018 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf01018_transform : affine01018=(NestedInteger.clearedAll 3 raw01018 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf01018_transform
theorem leaf01018_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01018=true := by decide +kernel
#print axioms leaf01018_sign
theorem leaf01018_log : RationalLog.accepts (2053017755/4294967296) (-1585128951/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01018_log
def leaf01018 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (449451932041/1000000000000) (2053017755/4294967296) (-1585128951/4294967296) 2 8 ![60,0,4] ![(7/40),0,(1/4)] ![(1/80),1,(1/4)] affine01018
theorem leaf01018_checked : FastNestedCellData.accepts 1 2 4 leaf01018=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (449451932041/1000000000000) (2053017755/4294967296) (-1585128951/4294967296) 2 8 ![60,0,4] ![(7/40),0,(1/4)] ![(1/80),1,(1/4)] 1658184952758924977537402745651200000000000 1148866672921015335387028584234718777573376 2556150259948628221113386663936000000000000 raw01018 affine01018
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01018_raw leaf01018_rectangular
    leaf01018_transform leaf01018_sign leaf01018_log
#print axioms leaf01018_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
