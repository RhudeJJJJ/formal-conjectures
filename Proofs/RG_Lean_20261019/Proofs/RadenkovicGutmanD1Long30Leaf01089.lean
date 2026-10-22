/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01089 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1158246131762652812096793739264000000000000 1249688317775990684340294608980629671378944 4975773269977615223437744144384000000000000))
theorem leaf01089_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1158246131762652812096793739264000000000000 1249688317775990684340294608980629671378944 4975773269977615223437744144384000000000000 raw01089=true := by decide +kernel
#print axioms leaf01089_raw
theorem leaf01089_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01089=true := by decide +kernel
#print axioms leaf01089_rectangular
def affine01089 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01089 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf01089_transform : affine01089=(NestedInteger.clearedAll 3 raw01089 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf01089_transform
theorem leaf01089_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01089=true := by decide +kernel
#print axioms leaf01089_sign
theorem leaf01089_log : RationalLog.accepts (3703818851/4294967296) (-317998409/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01089_log
def leaf01089 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (125577297233/500000000000) (3703818851/4294967296) (-317998409/4294967296) 1 8 ![60,0,4] ![(17/40),0,(1/2)] ![(3/80),1,(1/2)] affine01089
theorem leaf01089_checked : FastNestedCellData.accepts 1 2 4 leaf01089=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (125577297233/500000000000) (3703818851/4294967296) (-317998409/4294967296) 1 8 ![60,0,4] ![(17/40),0,(1/2)] ![(3/80),1,(1/2)] 1158246131762652812096793739264000000000000 1249688317775990684340294608980629671378944 4975773269977615223437744144384000000000000 raw01089 affine01089
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01089_raw leaf01089_rectangular
    leaf01089_transform leaf01089_sign leaf01089_log
#print axioms leaf01089_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
