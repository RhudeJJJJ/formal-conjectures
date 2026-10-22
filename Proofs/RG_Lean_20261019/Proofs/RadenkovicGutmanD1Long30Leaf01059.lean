/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01059 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 46510131700989734627555137290240000000000 43080762404679445186613419371104626016256 136692762547047117906177635123200000000000))
theorem leaf01059_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 46510131700989734627555137290240000000000 43080762404679445186613419371104626016256 136692762547047117906177635123200000000000 raw01059=true := by decide +kernel
#print axioms leaf01059_raw
theorem leaf01059_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01059=true := by decide +kernel
#print axioms leaf01059_rectangular
def affine01059 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01059 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01059_transform : affine01059=(NestedInteger.clearedAll 3 raw01059 (IntegerComputedClassCell.leftNumerator ![(47/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/160),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01059_transform
theorem leaf01059_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01059=true := by decide +kernel
#print axioms leaf01059_sign
theorem leaf01059_log : RationalLog.accepts (3024930905/4294967296) (-376406325/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01059_log
def leaf01059 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (63032982291/200000000000) (3024930905/4294967296) (-376406325/2147483648) 1 8 ![60,0,4] ![(47/160),0,(1/2)] ![(3/160),1,(1/2)] affine01059
theorem leaf01059_checked : FastNestedCellData.accepts 1 2 4 leaf01059=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (63032982291/200000000000) (3024930905/4294967296) (-376406325/2147483648) 1 8 ![60,0,4] ![(47/160),0,(1/2)] ![(3/160),1,(1/2)] 46510131700989734627555137290240000000000 43080762404679445186613419371104626016256 136692762547047117906177635123200000000000 raw01059 affine01059
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01059_raw leaf01059_rectangular
    leaf01059_transform leaf01059_sign leaf01059_log
#print axioms leaf01059_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
