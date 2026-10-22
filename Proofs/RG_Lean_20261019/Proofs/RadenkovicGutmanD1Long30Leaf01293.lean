/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01293 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 116617771824461494156787712000000000000 121218761475115889182121404232531705856 74900524744223766111183699968000000000000))
theorem leaf01293_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 116617771824461494156787712000000000000 121218761475115889182121404232531705856 74900524744223766111183699968000000000000 raw01293=true := by decide +kernel
#print axioms leaf01293_raw
theorem leaf01293_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01293=true := by decide +kernel
#print axioms leaf01293_rectangular
def affine01293 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01293 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01293_transform : affine01293=(NestedInteger.clearedAll 3 raw01293 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01293_transform
theorem leaf01293_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01293=true := by decide +kernel
#print axioms leaf01293_sign
theorem leaf01293_log : RationalLog.accepts (1114301411/1073741824) (79624595/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01293_log
def leaf01293 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (404599173/250000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(7/8)] ![(1/128),1,(1/16)] affine01293
theorem leaf01293_checked : FastNestedCellData.accepts 1 2 4 leaf01293=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (404599173/250000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(7/8)] ![(1/128),1,(1/16)] 116617771824461494156787712000000000000 121218761475115889182121404232531705856 74900524744223766111183699968000000000000 raw01293 affine01293
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01293_raw leaf01293_rectangular
    leaf01293_transform leaf01293_sign leaf01293_log
#print axioms leaf01293_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
