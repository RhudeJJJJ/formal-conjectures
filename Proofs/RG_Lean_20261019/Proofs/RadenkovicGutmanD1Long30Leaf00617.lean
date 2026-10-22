/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00617 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7031696046903085326401536000000000000 3744844177186053283469569872931848192 12492006676240414577524736000000000000))
theorem leaf00617_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7031696046903085326401536000000000000 3744844177186053283469569872931848192 12492006676240414577524736000000000000 raw00617=true := by decide +kernel
#print axioms leaf00617_raw
theorem leaf00617_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00617=true := by decide +kernel
#print axioms leaf00617_rectangular
def affine00617 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00617 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00617_transform : affine00617=(NestedInteger.clearedAll 3 raw00617 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00617_transform
theorem leaf00617_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00617=true := by decide +kernel
#print axioms leaf00617_sign
theorem leaf00617_log : RationalLog.accepts (13748457/33554432) (-1916075941/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00617_log
def leaf00617 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (74944808193/250000000000) (13748457/33554432) (-1916075941/4294967296) 2 8 ![60,0,4] ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)] affine00617
theorem leaf00617_checked : FastNestedCellData.accepts 1 2 4 leaf00617=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (74944808193/250000000000) (13748457/33554432) (-1916075941/4294967296) 2 8 ![60,0,4] ![(67/3200),0,(1/8)] ![(3/6400),1,(1/8)] 7031696046903085326401536000000000000 3744844177186053283469569872931848192 12492006676240414577524736000000000000 raw00617 affine00617
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00617_raw leaf00617_rectangular
    leaf00617_transform leaf00617_sign leaf00617_log
#print axioms leaf00617_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
