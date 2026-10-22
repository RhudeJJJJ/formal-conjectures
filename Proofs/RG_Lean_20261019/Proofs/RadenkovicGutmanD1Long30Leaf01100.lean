/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01100 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 452241483708662736766160076800000000000 529533872830678812772825701754593083392 2410655003217313276125773824000000000000))
theorem leaf01100_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 452241483708662736766160076800000000000 529533872830678812772825701754593083392 2410655003217313276125773824000000000000 raw01100=true := by decide +kernel
#print axioms leaf01100_raw
theorem leaf01100_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01100=true := by decide +kernel
#print axioms leaf01100_rectangular
def affine01100 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01100 (IntegerComputedClassCell.leftNumerator ![(17/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf01100_transform : affine01100=(NestedInteger.clearedAll 3 raw01100 (IntegerComputedClassCell.leftNumerator ![(17/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01100_transform
theorem leaf01100_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01100=true := by decide +kernel
#print axioms leaf01100_sign
theorem leaf01100_log : RationalLog.accepts (2061641015/2147483648) (-87605527/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01100_log
def leaf01100 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27457987151/125000000000) (2061641015/2147483648) (-87605527/4294967296) 1 8 ![60,0,4] ![(17/32),0,0] ![(1/32),1,(1/2)] affine01100
theorem leaf01100_checked : FastNestedCellData.accepts 1 2 4 leaf01100=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27457987151/125000000000) (2061641015/2147483648) (-87605527/4294967296) 1 8 ![60,0,4] ![(17/32),0,0] ![(1/32),1,(1/2)] 452241483708662736766160076800000000000 529533872830678812772825701754593083392 2410655003217313276125773824000000000000 raw01100 affine01100
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01100_raw leaf01100_rectangular
    leaf01100_transform leaf01100_sign leaf01100_log
#print axioms leaf01100_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
