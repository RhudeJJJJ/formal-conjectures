/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01329 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000))
theorem leaf01329_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01329=true := by decide +kernel
#print axioms leaf01329_raw
theorem leaf01329_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01329=true := by decide +kernel
#print axioms leaf01329_rectangular
def affine01329 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01329 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01329_transform : affine01329=(NestedInteger.clearedAll 3 raw01329 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01329_transform
theorem leaf01329_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01329=true := by decide +kernel
#print axioms leaf01329_sign
theorem leaf01329_log : RationalLog.accepts (4364709501/4294967296) (34591009/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01329_log
def leaf01329 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(15/16)] ![(1/128),1,(1/16)] affine01329
theorem leaf01329_checked : FastNestedCellData.accepts 1 2 4 leaf01329=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(15/16)] ![(1/128),1,(1/16)] 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01329 affine01329
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01329_raw leaf01329_rectangular
    leaf01329_transform leaf01329_sign leaf01329_log
#print axioms leaf01329_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
