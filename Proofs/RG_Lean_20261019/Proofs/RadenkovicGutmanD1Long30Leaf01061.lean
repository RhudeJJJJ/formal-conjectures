/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01061 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1745910687441744600993137426432000000000000 1688094243036218545382308624968521367945216 4458968419401266181921363197952000000000000))
theorem leaf01061_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1745910687441744600993137426432000000000000 1688094243036218545382308624968521367945216 4458968419401266181921363197952000000000000 raw01061=true := by decide +kernel
#print axioms leaf01061_raw
theorem leaf01061_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01061=true := by decide +kernel
#print axioms leaf01061_rectangular
def affine01061 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01061 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01061_transform : affine01061=(NestedInteger.clearedAll 3 raw01061 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01061_transform
theorem leaf01061_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01061=true := by decide +kernel
#print axioms leaf01061_sign
theorem leaf01061_log : RationalLog.accepts (3012321231/4294967296) (-761783323/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01061_log
def leaf01061 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (189292016029/500000000000) (3012321231/4294967296) (-761783323/4294967296) 1 8 ![60,0,4] ![(5/16),0,(1/16)] ![(3/160),1,(1/16)] affine01061
theorem leaf01061_checked : FastNestedCellData.accepts 1 2 4 leaf01061=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (189292016029/500000000000) (3012321231/4294967296) (-761783323/4294967296) 1 8 ![60,0,4] ![(5/16),0,(1/16)] ![(3/160),1,(1/16)] 1745910687441744600993137426432000000000000 1688094243036218545382308624968521367945216 4458968419401266181921363197952000000000000 raw01061 affine01061
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01061_raw leaf01061_rectangular
    leaf01061_transform leaf01061_sign leaf01061_log
#print axioms leaf01061_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
