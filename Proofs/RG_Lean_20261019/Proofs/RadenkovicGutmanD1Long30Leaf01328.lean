/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01328 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000))
theorem leaf01328_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01328=true := by decide +kernel
#print axioms leaf01328_raw
theorem leaf01328_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01328=true := by decide +kernel
#print axioms leaf01328_rectangular
def affine01328 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01328 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01328_transform : affine01328=(NestedInteger.clearedAll 3 raw01328 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01328_transform
theorem leaf01328_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01328=true := by decide +kernel
#print axioms leaf01328_sign
theorem leaf01328_log : RationalLog.accepts (4364709501/4294967296) (34591009/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01328_log
def leaf01328 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(7/8)] ![(1/128),1,(1/16)] affine01328
theorem leaf01328_checked : FastNestedCellData.accepts 1 2 4 leaf01328=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(7/8)] ![(1/128),1,(1/16)] 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01328 affine01328
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01328_raw leaf01328_rectangular
    leaf01328_transform leaf01328_sign leaf01328_log
#print axioms leaf01328_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
