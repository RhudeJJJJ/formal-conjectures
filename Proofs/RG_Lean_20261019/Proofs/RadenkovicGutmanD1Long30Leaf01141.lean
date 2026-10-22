/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01141 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 124875951166810770793784410112000000000000 159210393486620945146558441855941378834432 1469915421604640635023928590336000000000000))
theorem leaf01141_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 124875951166810770793784410112000000000000 159210393486620945146558441855941378834432 1469915421604640635023928590336000000000000 raw01141=true := by decide +kernel
#print axioms leaf01141_raw
theorem leaf01141_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01141=true := by decide +kernel
#print axioms leaf01141_rectangular
def affine01141 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01141 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01141_transform : affine01141=(NestedInteger.clearedAll 3 raw01141 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01141_transform
theorem leaf01141_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01141=true := by decide +kernel
#print axioms leaf01141_sign
theorem leaf01141_log : RationalLog.accepts (1235179847/1073741824) (150395801/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01141_log
def leaf01141 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (108312622037/1000000000000) (1235179847/1073741824) (150395801/2147483648) 0 8 ![60,0,4] ![(15/16),0,(1/2)] ![(1/16),1,(1/4)] affine01141
theorem leaf01141_checked : FastNestedCellData.accepts 1 2 4 leaf01141=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (108312622037/1000000000000) (1235179847/1073741824) (150395801/2147483648) 0 8 ![60,0,4] ![(15/16),0,(1/2)] ![(1/16),1,(1/4)] 124875951166810770793784410112000000000000 159210393486620945146558441855941378834432 1469915421604640635023928590336000000000000 raw01141 affine01141
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01141_raw leaf01141_rectangular
    leaf01141_transform leaf01141_sign leaf01141_log
#print axioms leaf01141_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
