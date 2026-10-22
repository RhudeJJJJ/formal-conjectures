/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01324 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000))
theorem leaf01324_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01324=true := by decide +kernel
#print axioms leaf01324_raw
theorem leaf01324_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01324=true := by decide +kernel
#print axioms leaf01324_rectangular
def affine01324 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01324 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01324_transform : affine01324=(NestedInteger.clearedAll 3 raw01324 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01324_transform
theorem leaf01324_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01324=true := by decide +kernel
#print axioms leaf01324_sign
theorem leaf01324_log : RationalLog.accepts (4376050291/4294967296) (40163563/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01324_log
def leaf01324 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(15/16)] ![(1/128),1,(1/16)] affine01324
theorem leaf01324_checked : FastNestedCellData.accepts 1 2 4 leaf01324=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(15/16)] ![(1/128),1,(1/16)] 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01324 affine01324
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01324_raw leaf01324_rectangular
    leaf01324_transform leaf01324_sign leaf01324_log
#print axioms leaf01324_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
