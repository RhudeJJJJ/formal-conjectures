/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00522 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4060490075986136341982417518592000000000000 2521095317709974865401320501588645147312128 11453297321488679002334973394944000000000000))
theorem leaf00522_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4060490075986136341982417518592000000000000 2521095317709974865401320501588645147312128 11453297321488679002334973394944000000000000 raw00522=true := by decide +kernel
#print axioms leaf00522_raw
theorem leaf00522_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00522=true := by decide +kernel
#print axioms leaf00522_rectangular
def affine00522 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00522 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00522_transform : affine00522=(NestedInteger.clearedAll 3 raw00522 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00522_transform
theorem leaf00522_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00522=true := by decide +kernel
#print axioms leaf00522_sign
theorem leaf00522_log : RationalLog.accepts (2185587847/4294967296) (-362688045/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00522_log
def leaf00522 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (220119608087/1000000000000) (2185587847/4294967296) (-362688045/1073741824) 1 8 ![60,0,4] ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00522
theorem leaf00522_checked : FastNestedCellData.accepts 1 2 4 leaf00522=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (220119608087/1000000000000) (2185587847/4294967296) (-362688045/1073741824) 1 8 ![60,0,4] ![(47/3200),0,(1/8)] ![(1/3200),1,(1/8)] 4060490075986136341982417518592000000000000 2521095317709974865401320501588645147312128 11453297321488679002334973394944000000000000 raw00522 affine00522
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00522_raw leaf00522_rectangular
    leaf00522_transform leaf00522_sign leaf00522_log
#print axioms leaf00522_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
