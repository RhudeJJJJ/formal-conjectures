/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01252 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3866355279836930052000527155200000000000 4148118328738102073739046785591344627712 989553101815864184093380968448000000000000))
theorem leaf01252_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3866355279836930052000527155200000000000 4148118328738102073739046785591344627712 989553101815864184093380968448000000000000 raw01252=true := by decide +kernel
#print axioms leaf01252_raw
theorem leaf01252_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01252=true := by decide +kernel
#print axioms leaf01252_rectangular
def affine01252 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01252 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01252_transform : affine01252=(NestedInteger.clearedAll 3 raw01252 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01252_transform
theorem leaf01252_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01252=true := by decide +kernel
#print axioms leaf01252_sign
theorem leaf01252_log : RationalLog.accepts (4588730165/4294967296) (142076213/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01252_log
def leaf01252 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2095955397/500000000000) (4588730165/4294967296) (142076213/4294967296) 0 8 ![60,0,4] ![(27/128),0,(3/4)] ![(1/128),1,(1/8)] affine01252
theorem leaf01252_checked : FastNestedCellData.accepts 1 2 4 leaf01252=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2095955397/500000000000) (4588730165/4294967296) (142076213/4294967296) 0 8 ![60,0,4] ![(27/128),0,(3/4)] ![(1/128),1,(1/8)] 3866355279836930052000527155200000000000 4148118328738102073739046785591344627712 989553101815864184093380968448000000000000 raw01252 affine01252
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01252_raw leaf01252_rectangular
    leaf01252_transform leaf01252_sign leaf01252_log
#print axioms leaf01252_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
