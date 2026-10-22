/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00197 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18783283590863007910868287488000000000000 16181177772165304675989852103953075929088 248300939145573381929953132544000000000000))
theorem leaf00197_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18783283590863007910868287488000000000000 16181177772165304675989852103953075929088 248300939145573381929953132544000000000000 raw00197=true := by decide +kernel
#print axioms leaf00197_raw
theorem leaf00197_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00197=true := by decide +kernel
#print axioms leaf00197_rectangular
def affine00197 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00197 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00197_transform : affine00197=(NestedInteger.clearedAll 3 raw00197 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00197_transform
theorem leaf00197_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00197=true := by decide +kernel
#print axioms leaf00197_sign
theorem leaf00197_log : RationalLog.accepts (868401437/1073741824) (-455805085/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00197_log
def leaf00197 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (32583803001/500000000000) (868401437/1073741824) (-455805085/4294967296) 1 8 ![60,0,4] ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00197
theorem leaf00197_checked : FastNestedCellData.accepts 1 2 4 leaf00197=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (32583803001/500000000000) (868401437/1073741824) (-455805085/4294967296) 1 8 ![60,0,4] ![(133/32000),0,(1/8)] ![(3/32000),1,(1/8)] 18783283590863007910868287488000000000000 16181177772165304675989852103953075929088 248300939145573381929953132544000000000000 raw00197 affine00197
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00197_raw leaf00197_rectangular
    leaf00197_transform leaf00197_sign leaf00197_log
#print axioms leaf00197_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
