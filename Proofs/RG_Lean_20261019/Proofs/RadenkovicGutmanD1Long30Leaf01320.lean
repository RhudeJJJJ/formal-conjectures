/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01320 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000))
theorem leaf01320_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01320=true := by decide +kernel
#print axioms leaf01320_raw
theorem leaf01320_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01320=true := by decide +kernel
#print axioms leaf01320_rectangular
def affine01320 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01320 (IntegerComputedClassCell.leftNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01320_transform : affine01320=(NestedInteger.clearedAll 3 raw01320 (IntegerComputedClassCell.leftNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01320_transform
theorem leaf01320_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01320=true := by decide +kernel
#print axioms leaf01320_sign
theorem leaf01320_log : RationalLog.accepts (4376050291/4294967296) (40163563/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01320_log
def leaf01320 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,0] ![(1/128),1,(1/2)] affine01320
theorem leaf01320_checked : FastNestedCellData.accepts 1 2 4 leaf01320=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,0] ![(1/128),1,(1/2)] 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01320 affine01320
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01320_raw leaf01320_rectangular
    leaf01320_transform leaf01320_sign leaf01320_log
#print axioms leaf01320_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
