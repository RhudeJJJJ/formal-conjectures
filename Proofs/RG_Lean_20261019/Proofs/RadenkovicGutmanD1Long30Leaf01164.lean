/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01164 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 20565437963483796342573105152000000000000 26317369638527087329237864122811366244352 368845310452669716396081414144000000000000))
theorem leaf01164_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 20565437963483796342573105152000000000000 26317369638527087329237864122811366244352 368845310452669716396081414144000000000000 raw01164=true := by decide +kernel
#print axioms leaf01164_raw
theorem leaf01164_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01164=true := by decide +kernel
#print axioms leaf01164_rectangular
def affine01164 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01164 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01164_transform : affine01164=(NestedInteger.clearedAll 3 raw01164 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01164_transform
theorem leaf01164_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01164=true := by decide +kernel
#print axioms leaf01164_sign
theorem leaf01164_log : RationalLog.accepts (1282545353/1073741824) (190800787/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01164_log
def leaf01164 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (35675348029/500000000000) (1282545353/1073741824) (190800787/2147483648) 0 8 ![60,0,4] ![(3/4),0,(15/16)] ![(1/16),1,(1/16)] affine01164
theorem leaf01164_checked : FastNestedCellData.accepts 1 2 4 leaf01164=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (35675348029/500000000000) (1282545353/1073741824) (190800787/2147483648) 0 8 ![60,0,4] ![(3/4),0,(15/16)] ![(1/16),1,(1/16)] 20565437963483796342573105152000000000000 26317369638527087329237864122811366244352 368845310452669716396081414144000000000000 raw01164 affine01164
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01164_raw leaf01164_rectangular
    leaf01164_transform leaf01164_sign leaf01164_log
#print axioms leaf01164_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
