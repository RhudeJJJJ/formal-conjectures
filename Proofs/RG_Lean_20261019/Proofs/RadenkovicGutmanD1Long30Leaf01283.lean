/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01283 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 9825517694341667112043413504000000000000 10289582468697203413186084953181372022784 4829498565116153554327184605184000000000000))
theorem leaf01283_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 9825517694341667112043413504000000000000 10289582468697203413186084953181372022784 4829498565116153554327184605184000000000000 raw01283=true := by decide +kernel
#print axioms leaf01283_raw
theorem leaf01283_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01283=true := by decide +kernel
#print axioms leaf01283_rectangular
def affine01283 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01283 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01283_transform : affine01283=(NestedInteger.clearedAll 3 raw01283 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01283_transform
theorem leaf01283_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01283=true := by decide +kernel
#print axioms leaf01283_sign
theorem leaf01283_log : RationalLog.accepts (4488258491/4294967296) (47266997/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01283_log
def leaf01283 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1065284763/500000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(7/8)] ![(1/128),1,(1/16)] affine01283
theorem leaf01283_checked : FastNestedCellData.accepts 1 2 4 leaf01283=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1065284763/500000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(7/8)] ![(1/128),1,(1/16)] 9825517694341667112043413504000000000000 10289582468697203413186084953181372022784 4829498565116153554327184605184000000000000 raw01283 affine01283
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01283_raw leaf01283_rectangular
    leaf01283_transform leaf01283_sign leaf01283_log
#print axioms leaf01283_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
