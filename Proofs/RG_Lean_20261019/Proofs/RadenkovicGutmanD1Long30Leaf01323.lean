/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01323 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000))
theorem leaf01323_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01323=true := by decide +kernel
#print axioms leaf01323_raw
theorem leaf01323_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01323=true := by decide +kernel
#print axioms leaf01323_rectangular
def affine01323 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01323 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01323_transform : affine01323=(NestedInteger.clearedAll 3 raw01323 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01323_transform
theorem leaf01323_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01323=true := by decide +kernel
#print axioms leaf01323_sign
theorem leaf01323_log : RationalLog.accepts (4376050291/4294967296) (40163563/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01323_log
def leaf01323 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(7/8)] ![(1/128),1,(1/16)] affine01323
theorem leaf01323_checked : FastNestedCellData.accepts 1 2 4 leaf01323=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (112334817/200000000000) (4376050291/4294967296) (40163563/4294967296) 0 8 ![60,0,4] ![(13/128),0,(7/8)] ![(1/128),1,(1/16)] 414442323953199398387082854400000000000 422503593365247080629676511576408981504 752221981837113030824052549222400000000000 raw01323 affine01323
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01323_raw leaf01323_rectangular
    leaf01323_transform leaf01323_sign leaf01323_log
#print axioms leaf01323_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
