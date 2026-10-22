/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01160 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 329673838552263931091459506176000000000000 422091887904657513455518264777460611547136 5904488104029333160899582623744000000000000))
theorem leaf01160_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 329673838552263931091459506176000000000000 422091887904657513455518264777460611547136 5904488104029333160899582623744000000000000 raw01160=true := by decide +kernel
#print axioms leaf01160_raw
theorem leaf01160_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01160=true := by decide +kernel
#print axioms leaf01160_rectangular
def affine01160 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01160 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/16),1,(1/2)]))
theorem leaf01160_transform : affine01160=(NestedInteger.clearedAll 3 raw01160 (IntegerComputedClassCell.leftNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/4),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01160_transform
theorem leaf01160_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01160=true := by decide +kernel
#print axioms leaf01160_sign
theorem leaf01160_log : RationalLog.accepts (5132106149/4294967296) (191203557/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01160_log
def leaf01160 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (35743309197/500000000000) (5132106149/4294967296) (191203557/2147483648) 0 8 ![60,0,4] ![(3/4),0,0] ![(1/16),1,(1/2)] affine01160
theorem leaf01160_checked : FastNestedCellData.accepts 1 2 4 leaf01160=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (35743309197/500000000000) (5132106149/4294967296) (191203557/2147483648) 0 8 ![60,0,4] ![(3/4),0,0] ![(1/16),1,(1/2)] 329673838552263931091459506176000000000000 422091887904657513455518264777460611547136 5904488104029333160899582623744000000000000 raw01160 affine01160
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01160_raw leaf01160_rectangular
    leaf01160_transform leaf01160_sign leaf01160_log
#print axioms leaf01160_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
