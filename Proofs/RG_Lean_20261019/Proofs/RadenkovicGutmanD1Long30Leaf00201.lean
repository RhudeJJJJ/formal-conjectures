/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00201 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 616782802414962524727346724864000000000000 456201136644828926421563864709927593312256 3411016641868357026557686972416000000000000))
theorem leaf00201_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 616782802414962524727346724864000000000000 456201136644828926421563864709927593312256 3411016641868357026557686972416000000000000 raw00201=true := by decide +kernel
#print axioms leaf00201_raw
theorem leaf00201_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00201=true := by decide +kernel
#print axioms leaf00201_rectangular
def affine00201 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00201 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00201_transform : affine00201=(NestedInteger.clearedAll 3 raw00201 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00201_transform
theorem leaf00201_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00201=true := by decide +kernel
#print axioms leaf00201_sign
theorem leaf00201_log : RationalLog.accepts (2802006749/4294967296) (-917207663/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00201_log
def leaf00201 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (66871725433/500000000000) (2802006749/4294967296) (-917207663/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)] affine00201
theorem leaf00201_checked : FastNestedCellData.accepts 1 2 4 leaf00201=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (66871725433/500000000000) (2802006749/4294967296) (-917207663/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/16)] ![(3/32000),1,(1/16)] 616782802414962524727346724864000000000000 456201136644828926421563864709927593312256 3411016641868357026557686972416000000000000 raw00201 affine00201
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00201_raw leaf00201_rectangular
    leaf00201_transform leaf00201_sign leaf00201_log
#print axioms leaf00201_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
