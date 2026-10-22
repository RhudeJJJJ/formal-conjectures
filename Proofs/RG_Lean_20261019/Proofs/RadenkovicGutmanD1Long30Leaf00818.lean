/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00818 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1348903162290862710207807488000000000000 766699724191874934882134781305819234304 2559789826803773633376288768000000000000))
theorem leaf00818_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1348903162290862710207807488000000000000 766699724191874934882134781305819234304 2559789826803773633376288768000000000000 raw00818=true := by decide +kernel
#print axioms leaf00818_raw
theorem leaf00818_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00818=true := by decide +kernel
#print axioms leaf00818_rectangular
def affine00818 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00818 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00818_transform : affine00818=(NestedInteger.clearedAll 3 raw00818 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00818_transform
theorem leaf00818_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00818=true := by decide +kernel
#print axioms leaf00818_sign
theorem leaf00818_log : RationalLog.accepts (29352329/67108864) (-887924653/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00818_log
def leaf00818 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (299516669753/1000000000000) (29352329/67108864) (-887924653/2147483648) 2 8 ![60,0,4] ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)] affine00818
theorem leaf00818_checked : FastNestedCellData.accepts 1 2 4 leaf00818=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (299516669753/1000000000000) (29352329/67108864) (-887924653/2147483648) 2 8 ![60,0,4] ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)] 1348903162290862710207807488000000000000 766699724191874934882134781305819234304 2559789826803773633376288768000000000000 raw00818 affine00818
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00818_raw leaf00818_rectangular
    leaf00818_transform leaf00818_sign leaf00818_log
#print axioms leaf00818_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
