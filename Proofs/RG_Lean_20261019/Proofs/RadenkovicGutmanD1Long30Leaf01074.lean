/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01074 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5340733769519740524966250020864000000000000 5352113173819992147789398804300686046527488 18486048215780068603606620700672000000000000))
theorem leaf01074_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5340733769519740524966250020864000000000000 5352113173819992147789398804300686046527488 18486048215780068603606620700672000000000000 raw01074=true := by decide +kernel
#print axioms leaf01074_raw
theorem leaf01074_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01074=true := by decide +kernel
#print axioms leaf01074_rectangular
def affine01074 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01074 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01074_transform : affine01074=(NestedInteger.clearedAll 3 raw01074 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01074_transform
theorem leaf01074_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01074=true := by decide +kernel
#print axioms leaf01074_sign
theorem leaf01074_log : RationalLog.accepts (3337763383/4294967296) (-270736507/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01074_log
def leaf01074 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (289521757779/1000000000000) (3337763383/4294967296) (-270736507/2147483648) 1 8 ![60,0,4] ![(7/20),0,(1/2)] ![(3/160),1,(1/2)] affine01074
theorem leaf01074_checked : FastNestedCellData.accepts 1 2 4 leaf01074=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (289521757779/1000000000000) (3337763383/4294967296) (-270736507/2147483648) 1 8 ![60,0,4] ![(7/20),0,(1/2)] ![(3/160),1,(1/2)] 5340733769519740524966250020864000000000000 5352113173819992147789398804300686046527488 18486048215780068603606620700672000000000000 raw01074 affine01074
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01074_raw leaf01074_rectangular
    leaf01074_transform leaf01074_sign leaf01074_log
#print axioms leaf01074_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
