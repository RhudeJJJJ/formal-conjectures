/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01284 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2456379421279573768797159424000000000000 2572395614754417717540100706826868228096 1207374641276628773152441237504000000000000))
theorem leaf01284_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2456379421279573768797159424000000000000 2572395614754417717540100706826868228096 1207374641276628773152441237504000000000000 raw01284=true := by decide +kernel
#print axioms leaf01284_raw
theorem leaf01284_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01284=true := by decide +kernel
#print axioms leaf01284_rectangular
def affine01284 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01284 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01284_transform : affine01284=(NestedInteger.clearedAll 3 raw01284 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01284_transform
theorem leaf01284_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01284=true := by decide +kernel
#print axioms leaf01284_sign
theorem leaf01284_log : RationalLog.accepts (4488258491/4294967296) (47266997/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01284_log
def leaf01284 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (532642381/250000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(15/16)] ![(1/128),1,(1/16)] affine01284
theorem leaf01284_checked : FastNestedCellData.accepts 1 2 4 leaf01284=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (532642381/250000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(15/16)] ![(1/128),1,(1/16)] 2456379421279573768797159424000000000000 2572395614754417717540100706826868228096 1207374641276628773152441237504000000000000 raw01284 affine01284
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01284_raw leaf01284_rectangular
    leaf01284_transform leaf01284_sign leaf01284_log
#print axioms leaf01284_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
