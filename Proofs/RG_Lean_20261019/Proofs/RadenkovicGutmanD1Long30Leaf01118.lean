/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01118 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 799077541510444705584766779392000000000000 958316829022462751245879550362554011222016 5530697700842333822000711073792000000000000))
theorem leaf01118_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 799077541510444705584766779392000000000000 958316829022462751245879550362554011222016 5530697700842333822000711073792000000000000 raw01118=true := by decide +kernel
#print axioms leaf01118_raw
theorem leaf01118_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01118=true := by decide +kernel
#print axioms leaf01118_rectangular
def affine01118 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01118 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01118_transform : affine01118=(NestedInteger.clearedAll 3 raw01118 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01118_transform
theorem leaf01118_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01118=true := by decide +kernel
#print axioms leaf01118_sign
theorem leaf01118_log : RationalLog.accepts (4390168871/4294967296) (11770225/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01118_log
def leaf01118 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (86636160649/500000000000) (4390168871/4294967296) (11770225/1073741824) 0 8 ![60,0,4] ![(5/8),0,(7/8)] ![(1/16),1,(1/16)] affine01118
theorem leaf01118_checked : FastNestedCellData.accepts 1 2 4 leaf01118=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (86636160649/500000000000) (4390168871/4294967296) (11770225/1073741824) 0 8 ![60,0,4] ![(5/8),0,(7/8)] ![(1/16),1,(1/16)] 799077541510444705584766779392000000000000 958316829022462751245879550362554011222016 5530697700842333822000711073792000000000000 raw01118 affine01118
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01118_raw leaf01118_rectangular
    leaf01118_transform leaf01118_sign leaf01118_log
#print axioms leaf01118_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
