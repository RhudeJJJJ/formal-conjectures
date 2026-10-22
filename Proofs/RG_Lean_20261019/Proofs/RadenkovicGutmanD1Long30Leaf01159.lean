/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01159 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 58024457741497559447450419200000000000 74357151137340079463755641940799913984 923403271486224461544502067200000000000))
theorem leaf01159_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 58024457741497559447450419200000000000 74357151137340079463755641940799913984 923403271486224461544502067200000000000 raw01159=true := by decide +kernel
#print axioms leaf01159_raw
theorem leaf01159_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01159=true := by decide +kernel
#print axioms leaf01159_rectangular
def affine01159 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01159 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01159_transform : affine01159=(NestedInteger.clearedAll 3 raw01159 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01159_transform
theorem leaf01159_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01159=true := by decide +kernel
#print axioms leaf01159_sign
theorem leaf01159_log : RationalLog.accepts (636717317/536870912) (366292219/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01159_log
def leaf01159 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4026255561/50000000000) (636717317/536870912) (366292219/4294967296) 0 8 ![60,0,4] ![(13/16),0,(15/16)] ![(1/16),1,(1/16)] affine01159
theorem leaf01159_checked : FastNestedCellData.accepts 1 2 4 leaf01159=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4026255561/50000000000) (636717317/536870912) (366292219/4294967296) 0 8 ![60,0,4] ![(13/16),0,(15/16)] ![(1/16),1,(1/16)] 58024457741497559447450419200000000000 74357151137340079463755641940799913984 923403271486224461544502067200000000000 raw01159 affine01159
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01159_raw leaf01159_rectangular
    leaf01159_transform leaf01159_sign leaf01159_log
#print axioms leaf01159_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
