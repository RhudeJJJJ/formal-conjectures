/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00267 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 260855831443218449111921459200000000000 212273612324939733521858349683773014016 2345498767997376331095683891200000000000))
theorem leaf00267_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 260855831443218449111921459200000000000 212273612324939733521858349683773014016 2345498767997376331095683891200000000000 raw00267=true := by decide +kernel
#print axioms leaf00267_raw
theorem leaf00267_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00267=true := by decide +kernel
#print axioms leaf00267_rectangular
def affine00267 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00267 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00267_transform : affine00267=(NestedInteger.clearedAll 3 raw00267 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00267_transform
theorem leaf00267_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00267=true := by decide +kernel
#print axioms leaf00267_sign
theorem leaf00267_log : RationalLog.accepts (400625557/536870912) (-78579239/536870912) 1 8=true := by decide +kernel
#print axioms leaf00267_log
def leaf00267 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9050254693/100000000000) (400625557/536870912) (-78579239/536870912) 1 8 ![60,0,4] ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00267
theorem leaf00267_checked : FastNestedCellData.accepts 1 2 4 leaf00267=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9050254693/100000000000) (400625557/536870912) (-78579239/536870912) 1 8 ![60,0,4] ![(37/6400),0,(1/8)] ![(1/6400),1,(1/8)] 260855831443218449111921459200000000000 212273612324939733521858349683773014016 2345498767997376331095683891200000000000 raw00267 affine00267
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00267_raw leaf00267_rectangular
    leaf00267_transform leaf00267_sign leaf00267_log
#print axioms leaf00267_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
