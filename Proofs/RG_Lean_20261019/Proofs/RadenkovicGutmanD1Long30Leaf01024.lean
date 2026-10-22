/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01024 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 397707914949105123036361654272000000000000 301467278315070638981584982592452240080896 873928063888848665373015277568000000000000))
theorem leaf01024_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 397707914949105123036361654272000000000000 301467278315070638981584982592452240080896 873928063888848665373015277568000000000000 raw01024=true := by decide +kernel
#print axioms leaf01024_raw
theorem leaf01024_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01024=true := by decide +kernel
#print axioms leaf01024_rectangular
def affine01024 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01024 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf01024_transform : affine01024=(NestedInteger.clearedAll 3 raw01024 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf01024_transform
theorem leaf01024_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01024=true := by decide +kernel
#print axioms leaf01024_sign
theorem leaf01024_log : RationalLog.accepts (1210312537/2147483648) (-1231406113/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01024_log
def leaf01024 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (172478314161/500000000000) (1210312537/2147483648) (-1231406113/4294967296) 1 8 ![60,0,4] ![(3/16),0,(1/2)] ![(1/80),1,(1/2)] affine01024
theorem leaf01024_checked : FastNestedCellData.accepts 1 2 4 leaf01024=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (172478314161/500000000000) (1210312537/2147483648) (-1231406113/4294967296) 1 8 ![60,0,4] ![(3/16),0,(1/2)] ![(1/80),1,(1/2)] 397707914949105123036361654272000000000000 301467278315070638981584982592452240080896 873928063888848665373015277568000000000000 raw01024 affine01024
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01024_raw leaf01024_rectangular
    leaf01024_transform leaf01024_sign leaf01024_log
#print axioms leaf01024_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
