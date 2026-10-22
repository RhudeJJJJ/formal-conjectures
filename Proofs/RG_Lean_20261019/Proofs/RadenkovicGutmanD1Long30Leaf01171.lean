/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01171 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 51138032108574542373146591232000000000000 63939880252625520203818567113013305802752 1441542818634940543560461582336000000000000))
theorem leaf01171_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 51138032108574542373146591232000000000000 63939880252625520203818567113013305802752 1441542818634940543560461582336000000000000 raw01171=true := by decide +kernel
#print axioms leaf01171_raw
theorem leaf01171_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01171=true := by decide +kernel
#print axioms leaf01171_rectangular
def affine01171 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01171 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01171_transform : affine01171=(NestedInteger.clearedAll 3 raw01171 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01171_transform
theorem leaf01171_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01171=true := by decide +kernel
#print axioms leaf01171_sign
theorem leaf01171_log : RationalLog.accepts (1285521827/1073741824) (3020153/33554432) 0 8=true := by decide +kernel
#print axioms leaf01171_log
def leaf01171 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (44355172407/1000000000000) (1285521827/1073741824) (3020153/33554432) 0 8 ![60,0,4] ![(9/16),0,(1/2)] ![(1/16),1,(1/4)] affine01171
theorem leaf01171_checked : FastNestedCellData.accepts 1 2 4 leaf01171=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (44355172407/1000000000000) (1285521827/1073741824) (3020153/33554432) 0 8 ![60,0,4] ![(9/16),0,(1/2)] ![(1/16),1,(1/4)] 51138032108574542373146591232000000000000 63939880252625520203818567113013305802752 1441542818634940543560461582336000000000000 raw01171 affine01171
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01171_raw leaf01171_rectangular
    leaf01171_transform leaf01171_sign leaf01171_log
#print axioms leaf01171_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
