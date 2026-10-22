/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00153 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 117927904328848254285859782656000000000000 111063235695321727085309534180055567040512 4343236438673200530366406852608000000000000))
theorem leaf00153_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 117927904328848254285859782656000000000000 111063235695321727085309534180055567040512 4343236438673200530366406852608000000000000 raw00153=true := by decide +kernel
#print axioms leaf00153_raw
theorem leaf00153_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00153=true := by decide +kernel
#print axioms leaf00153_rectangular
def affine00153 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00153 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00153_transform : affine00153=(NestedInteger.clearedAll 3 raw00153 (IntegerComputedClassCell.leftNumerator ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00153_transform
theorem leaf00153_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00153=true := by decide +kernel
#print axioms leaf00153_sign
theorem leaf00153_log : RationalLog.accepts (3944097503/4294967296) (-45754179/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00153_log
def leaf00153 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12785769007/500000000000) (3944097503/4294967296) (-45754179/1073741824) 1 8 ![60,0,4] ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)] affine00153
theorem leaf00153_checked : FastNestedCellData.accepts 1 2 4 leaf00153=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12785769007/500000000000) (3944097503/4294967296) (-45754179/1073741824) 1 8 ![60,0,4] ![(53/16000),0,(1/4)] ![(3/32000),1,(1/4)] 117927904328848254285859782656000000000000 111063235695321727085309534180055567040512 4343236438673200530366406852608000000000000 raw00153 affine00153
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00153_raw leaf00153_rectangular
    leaf00153_transform leaf00153_sign leaf00153_log
#print axioms leaf00153_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
