/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01125 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 417527023661311000117143142400000000000 520793368151867174660458052367383789568 3595179710367546246557387980800000000000))
theorem leaf01125_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 417527023661311000117143142400000000000 520793368151867174660458052367383789568 3595179710367546246557387980800000000000 raw01125=true := by decide +kernel
#print axioms leaf01125_raw
theorem leaf01125_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01125=true := by decide +kernel
#print axioms leaf01125_rectangular
def affine01125 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01125 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/16),1,(1/2)]))
theorem leaf01125_transform : affine01125=(NestedInteger.clearedAll 3 raw01125 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01125_transform
theorem leaf01125_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01125=true := by decide +kernel
#print axioms leaf01125_sign
theorem leaf01125_log : RationalLog.accepts (2339692591/2147483648) (184088287/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01125_log
def leaf01125 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3621469649/25000000000) (2339692591/2147483648) (184088287/4294967296) 0 8 ![60,0,4] ![(3/4),0,0] ![(1/16),1,(1/2)] affine01125
theorem leaf01125_checked : FastNestedCellData.accepts 1 2 4 leaf01125=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3621469649/25000000000) (2339692591/2147483648) (184088287/4294967296) 0 8 ![60,0,4] ![(3/4),0,0] ![(1/16),1,(1/2)] 417527023661311000117143142400000000000 520793368151867174660458052367383789568 3595179710367546246557387980800000000000 raw01125 affine01125
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01125_raw leaf01125_rectangular
    leaf01125_transform leaf01125_sign leaf01125_log
#print axioms leaf01125_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
