/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01101 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 156699794561859220230523951513600000000000 182168011542116809185027881932845400195072 857794790792130496323180612812800000000000))
theorem leaf01101_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 156699794561859220230523951513600000000000 182168011542116809185027881932845400195072 857794790792130496323180612812800000000000 raw01101=true := by decide +kernel
#print axioms leaf01101_raw
theorem leaf01101_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01101=true := by decide +kernel
#print axioms leaf01101_rectangular
def affine01101 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01101 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01101_transform : affine01101=(NestedInteger.clearedAll 3 raw01101 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01101_transform
theorem leaf01101_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01101=true := by decide +kernel
#print axioms leaf01101_sign
theorem leaf01101_log : RationalLog.accepts (4118405933/4294967296) (-45073297/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01101_log
def leaf01101 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42473564423/200000000000) (4118405933/4294967296) (-45073297/2147483648) 1 8 ![60,0,4] ![(17/32),0,(1/2)] ![(1/32),1,(1/4)] affine01101
theorem leaf01101_checked : FastNestedCellData.accepts 1 2 4 leaf01101=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42473564423/200000000000) (4118405933/4294967296) (-45073297/2147483648) 1 8 ![60,0,4] ![(17/32),0,(1/2)] ![(1/32),1,(1/4)] 156699794561859220230523951513600000000000 182168011542116809185027881932845400195072 857794790792130496323180612812800000000000 raw01101 affine01101
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01101_raw leaf01101_rectangular
    leaf01101_transform leaf01101_sign leaf01101_log
#print axioms leaf01101_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
