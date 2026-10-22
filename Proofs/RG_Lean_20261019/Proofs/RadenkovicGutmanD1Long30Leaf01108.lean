/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01108 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11344453052564275569068553011200000000000 13321575000584074563078655971940425007104 67692687440469840616117764096000000000000))
theorem leaf01108_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11344453052564275569068553011200000000000 13321575000584074563078655971940425007104 67692687440469840616117764096000000000000 raw01108=true := by decide +kernel
#print axioms leaf01108_raw
theorem leaf01108_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01108=true := by decide +kernel
#print axioms leaf01108_rectangular
def affine01108 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01108 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01108_transform : affine01108=(NestedInteger.clearedAll 3 raw01108 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01108_transform
theorem leaf01108_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01108=true := by decide +kernel
#print axioms leaf01108_sign
theorem leaf01108_log : RationalLog.accepts (2107085465/2147483648) (-40783037/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01108_log
def leaf01108 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49198722581/250000000000) (2107085465/2147483648) (-40783037/4294967296) 1 8 ![60,0,4] ![(9/16),0,(7/8)] ![(1/32),1,(1/16)] affine01108
theorem leaf01108_checked : FastNestedCellData.accepts 1 2 4 leaf01108=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49198722581/250000000000) (2107085465/2147483648) (-40783037/4294967296) 1 8 ![60,0,4] ![(9/16),0,(7/8)] ![(1/32),1,(1/16)] 11344453052564275569068553011200000000000 13321575000584074563078655971940425007104 67692687440469840616117764096000000000000 raw01108 affine01108
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01108_raw leaf01108_rectangular
    leaf01108_transform leaf01108_sign leaf01108_log
#print axioms leaf01108_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
