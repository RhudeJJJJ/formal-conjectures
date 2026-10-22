/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01055 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 29448460307043769643211685888000000000000 27483783365384053338465813145922129887232 67250215587519389562205896704000000000000))
theorem leaf01055_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 29448460307043769643211685888000000000000 27483783365384053338465813145922129887232 67250215587519389562205896704000000000000 raw01055=true := by decide +kernel
#print axioms leaf01055_raw
theorem leaf01055_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01055=true := by decide +kernel
#print axioms leaf01055_rectangular
def affine01055 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01055 (IntegerComputedClassCell.leftNumerator ![(47/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/160),0,0] ![(3/160),1,(1/16)]))
theorem leaf01055_transform : affine01055=(NestedInteger.clearedAll 3 raw01055 (IntegerComputedClassCell.leftNumerator ![(47/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/160),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01055_transform
theorem leaf01055_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01055=true := by decide +kernel
#print axioms leaf01055_sign
theorem leaf01055_log : RationalLog.accepts (2845519693/4294967296) (-442057617/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01055_log
def leaf01055 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (25542467713/62500000000) (2845519693/4294967296) (-442057617/2147483648) 1 8 ![60,0,4] ![(47/160),0,0] ![(3/160),1,(1/16)] affine01055
theorem leaf01055_checked : FastNestedCellData.accepts 1 2 4 leaf01055=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (25542467713/62500000000) (2845519693/4294967296) (-442057617/2147483648) 1 8 ![60,0,4] ![(47/160),0,0] ![(3/160),1,(1/16)] 29448460307043769643211685888000000000000 27483783365384053338465813145922129887232 67250215587519389562205896704000000000000 raw01055 affine01055
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01055_raw leaf01055_rectangular
    leaf01055_transform leaf01055_sign leaf01055_log
#print axioms leaf01055_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
