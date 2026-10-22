/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01327 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000))
theorem leaf01327_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01327=true := by decide +kernel
#print axioms leaf01327_raw
theorem leaf01327_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01327=true := by decide +kernel
#print axioms leaf01327_rectangular
def affine01327 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01327 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/32),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01327_transform : affine01327=(NestedInteger.clearedAll 3 raw01327 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/32),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01327_transform
theorem leaf01327_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01327=true := by decide +kernel
#print axioms leaf01327_sign
theorem leaf01327_log : RationalLog.accepts (4364709501/4294967296) (34591009/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01327_log
def leaf01327 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(3/4)] ![(1/128),1,(1/8)] affine01327
theorem leaf01327_checked : FastNestedCellData.accepts 1 2 4 leaf01327=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(3/4)] ![(1/128),1,(1/8)] 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01327 affine01327
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01327_raw leaf01327_rectangular
    leaf01327_transform leaf01327_sign leaf01327_log
#print axioms leaf01327_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
