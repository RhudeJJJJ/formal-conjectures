/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00340 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2288191133824875844900522819584000000000000 1339612649674989889205714856526028338102272 2699893743704818484618127736832000000000000))
theorem leaf00340_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2288191133824875844900522819584000000000000 1339612649674989889205714856526028338102272 2699893743704818484618127736832000000000000 raw00340=true := by decide +kernel
#print axioms leaf00340_raw
theorem leaf00340_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00340=true := by decide +kernel
#print axioms leaf00340_rectangular
def affine00340 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00340 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00340_transform : affine00340=(NestedInteger.clearedAll 3 raw00340 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00340_transform
theorem leaf00340_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00340=true := by decide +kernel
#print axioms leaf00340_sign
theorem leaf00340_log : RationalLog.accepts (840301579/2147483648) (-2014965057/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00340_log
def leaf00340 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (496172359671/1000000000000) (840301579/2147483648) (-2014965057/4294967296) 2 8 ![52,0,4] ![(11/80),0,(1/4)] ![(1/160),1,(1/4)] affine00340
theorem leaf00340_checked : FastNestedCellData.accepts 1 0 4 leaf00340=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (496172359671/1000000000000) (840301579/2147483648) (-2014965057/4294967296) 2 8 ![52,0,4] ![(11/80),0,(1/4)] ![(1/160),1,(1/4)] 2288191133824875844900522819584000000000000 1339612649674989889205714856526028338102272 2699893743704818484618127736832000000000000 raw00340 affine00340
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00340_raw leaf00340_rectangular
    leaf00340_transform leaf00340_sign leaf00340_log
#print axioms leaf00340_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
