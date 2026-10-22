/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01325 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000))
theorem leaf01325_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01325=true := by decide +kernel
#print axioms leaf01325_raw
theorem leaf01325_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01325=true := by decide +kernel
#print axioms leaf01325_rectangular
def affine01325 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01325 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/128),1,(1/2)]))
theorem leaf01325_transform : affine01325=(NestedInteger.clearedAll 3 raw01325 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01325_transform
theorem leaf01325_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01325=true := by decide +kernel
#print axioms leaf01325_sign
theorem leaf01325_log : RationalLog.accepts (4364709501/4294967296) (34591009/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01325_log
def leaf01325 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,0] ![(1/128),1,(1/2)] affine01325
theorem leaf01325_checked : FastNestedCellData.accepts 1 2 4 leaf01325=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,0] ![(1/128),1,(1/2)] 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01325 affine01325
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01325_raw leaf01325_rectangular
    leaf01325_transform leaf01325_sign leaf01325_log
#print axioms leaf01325_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
