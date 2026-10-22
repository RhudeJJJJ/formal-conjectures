/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01321 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000))
theorem leaf01321_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01321=true := by decide +kernel
#print axioms leaf01321_raw
theorem leaf01321_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01321=true := by decide +kernel
#print axioms leaf01321_rectangular
def affine01321 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01321 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01321_transform : affine01321=(NestedInteger.clearedAll 3 raw01321 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01321_transform
theorem leaf01321_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01321=true := by decide +kernel
#print axioms leaf01321_sign
theorem leaf01321_log : RationalLog.accepts (4376050291/4294967296) (40163563/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01321_log
def leaf01321 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(1/2)] ![(1/128),1,(1/4)] affine01321
theorem leaf01321_checked : FastNestedCellData.accepts 1 2 4 leaf01321=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(1/2)] ![(1/128),1,(1/4)] 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01321 affine01321
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01321_raw leaf01321_rectangular
    leaf01321_transform leaf01321_sign leaf01321_log
#print axioms leaf01321_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
