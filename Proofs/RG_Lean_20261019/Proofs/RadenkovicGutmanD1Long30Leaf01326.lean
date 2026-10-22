/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01326 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000))
theorem leaf01326_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01326=true := by decide +kernel
#print axioms leaf01326_raw
theorem leaf01326_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01326=true := by decide +kernel
#print axioms leaf01326_rectangular
def affine01326 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01326 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01326_transform : affine01326=(NestedInteger.clearedAll 3 raw01326 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01326_transform
theorem leaf01326_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01326=true := by decide +kernel
#print axioms leaf01326_sign
theorem leaf01326_log : RationalLog.accepts (4364709501/4294967296) (34591009/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01326_log
def leaf01326 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(1/2)] ![(1/128),1,(1/4)] affine01326
theorem leaf01326_checked : FastNestedCellData.accepts 1 2 4 leaf01326=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (448588259/1000000000000) (4364709501/4294967296) (34591009/4294967296) 0 8 ![60,0,4] ![(3/32),0,(1/2)] ![(1/128),1,(1/4)] 8274992808243935431092076544000000000000 8413135496562231465359106574804347518976 18754693926490464533890323185664000000000000 raw01326 affine01326
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01326_raw leaf01326_rectangular
    leaf01326_transform leaf01326_sign leaf01326_log
#print axioms leaf01326_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
