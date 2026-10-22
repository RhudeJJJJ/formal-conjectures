/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01174 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 51129201916205482165755969536000000000000 63927258769514914958103843970276336336896 1441507174055460270566314868736000000000000))
theorem leaf01174_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 51129201916205482165755969536000000000000 63927258769514914958103843970276336336896 1441507174055460270566314868736000000000000 raw01174=true := by decide +kernel
#print axioms leaf01174_raw
theorem leaf01174_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01174=true := by decide +kernel
#print axioms leaf01174_rectangular
def affine01174 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01174 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01174_transform : affine01174=(NestedInteger.clearedAll 3 raw01174 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/16),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01174_transform
theorem leaf01174_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01174=true := by decide +kernel
#print axioms leaf01174_sign
theorem leaf01174_log : RationalLog.accepts (5141997871/4294967296) (386542233/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01174_log
def leaf01174 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (11086878359/250000000000) (5141997871/4294967296) (386542233/4294967296) 0 8 ![60,0,4] ![(9/16),0,(15/16)] ![(1/16),1,(1/16)] affine01174
theorem leaf01174_checked : FastNestedCellData.accepts 1 2 4 leaf01174=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (11086878359/250000000000) (5141997871/4294967296) (386542233/4294967296) 0 8 ![60,0,4] ![(9/16),0,(15/16)] ![(1/16),1,(1/16)] 51129201916205482165755969536000000000000 63927258769514914958103843970276336336896 1441507174055460270566314868736000000000000 raw01174 affine01174
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01174_raw leaf01174_rectangular
    leaf01174_transform leaf01174_sign leaf01174_log
#print axioms leaf01174_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
