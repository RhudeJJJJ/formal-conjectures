/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00672 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 82109614997972368795291038515200000000000 39617930486351669392375180025522691244032 111257041034383076088015224832000000000000))
theorem leaf00672_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 82109614997972368795291038515200000000000 39617930486351669392375180025522691244032 111257041034383076088015224832000000000000 raw00672=true := by decide +kernel
#print axioms leaf00672_raw
theorem leaf00672_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00672=true := by decide +kernel
#print axioms leaf00672_rectangular
def affine00672 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00672 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00672_transform : affine00672=(NestedInteger.clearedAll 3 raw00672 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00672_transform
theorem leaf00672_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00672=true := by decide +kernel
#print axioms leaf00672_sign
theorem leaf00672_log : RationalLog.accepts (382039215/1073741824) (-554792539/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00672_log
def leaf00672 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (356093691851/1000000000000) (382039215/1073741824) (-554792539/1073741824) 2 8 ![60,0,4] ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00672
theorem leaf00672_checked : FastNestedCellData.accepts 1 2 4 leaf00672=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (356093691851/1000000000000) (382039215/1073741824) (-554792539/1073741824) 2 8 ![60,0,4] ![(167/6400),0,(1/8)] ![(3/6400),1,(1/8)] 82109614997972368795291038515200000000000 39617930486351669392375180025522691244032 111257041034383076088015224832000000000000 raw00672 affine00672
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00672_raw leaf00672_rectangular
    leaf00672_transform leaf00672_sign leaf00672_log
#print axioms leaf00672_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
