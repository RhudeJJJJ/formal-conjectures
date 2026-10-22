/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00209 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18679156663717868493852377088000000000000 17979622170078278364226131905964675170304 1109744589532415613205907243008000000000000))
theorem leaf00209_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18679156663717868493852377088000000000000 17979622170078278364226131905964675170304 1109744589532415613205907243008000000000000 raw00209=true := by decide +kernel
#print axioms leaf00209_raw
theorem leaf00209_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00209=true := by decide +kernel
#print axioms leaf00209_rectangular
def affine00209 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00209 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00209_transform : affine00209=(NestedInteger.clearedAll 3 raw00209 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00209_transform
theorem leaf00209_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00209=true := by decide +kernel
#print axioms leaf00209_sign
theorem leaf00209_log : RationalLog.accepts (4068209311/4294967296) (-116481721/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00209_log
def leaf00209 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4050396447/250000000000) (4068209311/4294967296) (-116481721/4294967296) 1 8 ![60,0,4] ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00209
theorem leaf00209_checked : FastNestedCellData.accepts 1 2 4 leaf00209=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4050396447/250000000000) (4068209311/4294967296) (-116481721/4294967296) 1 8 ![60,0,4] ![(139/32000),0,(1/2)] ![(3/32000),1,(1/2)] 18679156663717868493852377088000000000000 17979622170078278364226131905964675170304 1109744589532415613205907243008000000000000 raw00209 affine00209
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00209_raw leaf00209_rectangular
    leaf00209_transform leaf00209_sign leaf00209_log
#print axioms leaf00209_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
