/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01170 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 51147668507822893524242661376000000000000 63953545751314763754345276352084876197888 1441579261452969692638570610688000000000000))
theorem leaf01170_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 51147668507822893524242661376000000000000 63953545751314763754345276352084876197888 1441579261452969692638570610688000000000000 raw01170=true := by decide +kernel
#print axioms leaf01170_raw
theorem leaf01170_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01170=true := by decide +kernel
#print axioms leaf01170_rectangular
def affine01170 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01170 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf01170_transform : affine01170=(NestedInteger.clearedAll 3 raw01170 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01170_transform
theorem leaf01170_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01170=true := by decide +kernel
#print axioms leaf01170_sign
theorem leaf01170_log : RationalLog.accepts (1285544037/1073741824) (193308343/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01170_log
def leaf01170 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (44363530651/1000000000000) (1285544037/1073741824) (193308343/2147483648) 0 8 ![60,0,4] ![(9/16),0,0] ![(1/16),1,(1/2)] affine01170
theorem leaf01170_checked : FastNestedCellData.accepts 1 2 4 leaf01170=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (44363530651/1000000000000) (1285544037/1073741824) (193308343/2147483648) 0 8 ![60,0,4] ![(9/16),0,0] ![(1/16),1,(1/2)] 51147668507822893524242661376000000000000 63953545751314763754345276352084876197888 1441579261452969692638570610688000000000000 raw01170 affine01170
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01170_raw leaf01170_rectangular
    leaf01170_transform leaf01170_sign leaf01170_log
#print axioms leaf01170_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
