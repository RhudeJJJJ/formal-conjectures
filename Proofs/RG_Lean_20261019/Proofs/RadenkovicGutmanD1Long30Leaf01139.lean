/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01139 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 136043195831607709790873059328000000000000 172238198966391601644706119851384563040256 1459662295414623733717665841152000000000000))
theorem leaf01139_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 136043195831607709790873059328000000000000 172238198966391601644706119851384563040256 1459662295414623733717665841152000000000000 raw01139=true := by decide +kernel
#print axioms leaf01139_raw
theorem leaf01139_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01139=true := by decide +kernel
#print axioms leaf01139_rectangular
def affine01139 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01139 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01139_transform : affine01139=(NestedInteger.clearedAll 3 raw01139 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01139_transform
theorem leaf01139_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01139=true := by decide +kernel
#print axioms leaf01139_sign
theorem leaf01139_log : RationalLog.accepts (2431874907/2147483648) (267073449/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01139_log
def leaf01139 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (58999331389/500000000000) (2431874907/2147483648) (267073449/4294967296) 0 8 ![60,0,4] ![(7/8),0,(15/16)] ![(1/16),1,(1/16)] affine01139
theorem leaf01139_checked : FastNestedCellData.accepts 1 2 4 leaf01139=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (58999331389/500000000000) (2431874907/2147483648) (267073449/4294967296) 0 8 ![60,0,4] ![(7/8),0,(15/16)] ![(1/16),1,(1/16)] 136043195831607709790873059328000000000000 172238198966391601644706119851384563040256 1459662295414623733717665841152000000000000 raw01139 affine01139
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01139_raw leaf01139_rectangular
    leaf01139_transform leaf01139_sign leaf01139_log
#print axioms leaf01139_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
