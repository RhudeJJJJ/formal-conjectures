/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01322 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000))
theorem leaf01322_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01322=true := by decide +kernel
#print axioms leaf01322_raw
theorem leaf01322_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01322=true := by decide +kernel
#print axioms leaf01322_rectangular
def affine01322 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01322 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01322_transform : affine01322=(NestedInteger.clearedAll 3 raw01322 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01322_transform
theorem leaf01322_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01322=true := by decide +kernel
#print axioms leaf01322_sign
theorem leaf01322_log : RationalLog.accepts (4376050291/4294967296) (40163563/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01322_log
def leaf01322 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(3/4)] ![(1/128),1,(1/8)] affine01322
theorem leaf01322_checked : FastNestedCellData.accepts 1 2 4 leaf01322=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(3/4)] ![(1/128),1,(1/8)] 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01322 affine01322
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01322_raw leaf01322_rectangular
    leaf01322_transform leaf01322_sign leaf01322_log
#print axioms leaf01322_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
