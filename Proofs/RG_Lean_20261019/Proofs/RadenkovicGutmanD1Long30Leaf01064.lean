/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01064 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 22109609166327317333188542464000000000000 21070838719298778165752104681136757669888 68672129437107353610105126912000000000000))
theorem leaf01064_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 22109609166327317333188542464000000000000 21070838719298778165752104681136757669888 68672129437107353610105126912000000000000 raw01064=true := by decide +kernel
#print axioms leaf01064_raw
theorem leaf01064_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01064=true := by decide +kernel
#print axioms leaf01064_rectangular
def affine01064 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01064 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01064_transform : affine01064=(NestedInteger.clearedAll 3 raw01064 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01064_transform
theorem leaf01064_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01064=true := by decide +kernel
#print axioms leaf01064_sign
theorem leaf01064_log : RationalLog.accepts (783034167/1073741824) (-339010943/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01064_log
def leaf01064 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (76708116131/250000000000) (783034167/1073741824) (-339010943/2147483648) 1 8 ![60,0,4] ![(5/16),0,(1/2)] ![(3/160),1,(1/2)] affine01064
theorem leaf01064_checked : FastNestedCellData.accepts 1 2 4 leaf01064=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (76708116131/250000000000) (783034167/1073741824) (-339010943/2147483648) 1 8 ![60,0,4] ![(5/16),0,(1/2)] ![(3/160),1,(1/2)] 22109609166327317333188542464000000000000 21070838719298778165752104681136757669888 68672129437107353610105126912000000000000 raw01064 affine01064
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01064_raw leaf01064_rectangular
    leaf01064_transform leaf01064_sign leaf01064_log
#print axioms leaf01064_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
