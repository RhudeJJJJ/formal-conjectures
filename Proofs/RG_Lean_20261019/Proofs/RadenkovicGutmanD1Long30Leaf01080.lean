/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01080 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 355849999479832482212543987712000000000000 378022999357637964149842097230041178963968 1224759999529244002737836785664000000000000))
theorem leaf01080_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 355849999479832482212543987712000000000000 378022999357637964149842097230041178963968 1224759999529244002737836785664000000000000 raw01080=true := by decide +kernel
#print axioms leaf01080_raw
theorem leaf01080_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01080=true := by decide +kernel
#print axioms leaf01080_rectangular
def affine01080 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01080 (IntegerComputedClassCell.leftNumerator ![(31/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/80),0,0] ![(3/80),1,(1/16)]))
theorem leaf01080_transform : affine01080=(NestedInteger.clearedAll 3 raw01080 (IntegerComputedClassCell.leftNumerator ![(31/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,0] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/80),0,0] ![(3/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01080_transform
theorem leaf01080_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01080=true := by decide +kernel
#print axioms leaf01080_sign
theorem leaf01080_log : RationalLog.accepts (3486481637/4294967296) (-447859555/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01080_log
def leaf01080 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (77162668503/250000000000) (3486481637/4294967296) (-447859555/4294967296) 1 8 ![60,0,4] ![(31/80),0,0] ![(3/80),1,(1/16)] affine01080
theorem leaf01080_checked : FastNestedCellData.accepts 1 2 4 leaf01080=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (77162668503/250000000000) (3486481637/4294967296) (-447859555/4294967296) 1 8 ![60,0,4] ![(31/80),0,0] ![(3/80),1,(1/16)] 355849999479832482212543987712000000000000 378022999357637964149842097230041178963968 1224759999529244002737836785664000000000000 raw01080 affine01080
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01080_raw leaf01080_rectangular
    leaf01080_transform leaf01080_sign leaf01080_log
#print axioms leaf01080_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
