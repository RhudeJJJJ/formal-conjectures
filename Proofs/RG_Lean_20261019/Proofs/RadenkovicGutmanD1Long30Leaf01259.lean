/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01259 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 4372542276070178668746375168000000000000 4671680874999998083515158531969875181568 1231796287693933637483968331776000000000000))
theorem leaf01259_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 4372542276070178668746375168000000000000 4671680874999998083515158531969875181568 1231796287693933637483968331776000000000000 raw01259=true := by decide +kernel
#print axioms leaf01259_raw
theorem leaf01259_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01259=true := by decide +kernel
#print axioms leaf01259_rectangular
def affine01259 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01259 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/64),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01259_transform : affine01259=(NestedInteger.clearedAll 3 raw01259 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/64),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01259_transform
theorem leaf01259_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01259=true := by decide +kernel
#print axioms leaf01259_sign
theorem leaf01259_log : RationalLog.accepts (4571461147/4294967296) (133979225/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01259_log
def leaf01259 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (948143967/250000000000) (4571461147/4294967296) (133979225/4294967296) 0 8 ![60,0,4] ![(13/64),0,(15/16)] ![(1/128),1,(1/16)] affine01259
theorem leaf01259_checked : FastNestedCellData.accepts 1 2 4 leaf01259=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (948143967/250000000000) (4571461147/4294967296) (133979225/4294967296) 0 8 ![60,0,4] ![(13/64),0,(15/16)] ![(1/128),1,(1/16)] 4372542276070178668746375168000000000000 4671680874999998083515158531969875181568 1231796287693933637483968331776000000000000 raw01259 affine01259
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01259_raw leaf01259_rectangular
    leaf01259_transform leaf01259_sign leaf01259_log
#print axioms leaf01259_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
