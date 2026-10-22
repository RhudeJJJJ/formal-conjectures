/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00175 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3925162792165404424408976588800000000000 1154392608959767623109301197915291648 3390748700373480824740249600000000000))
theorem leaf00175_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3925162792165404424408976588800000000000 1154392608959767623109301197915291648 3390748700373480824740249600000000000 raw00175=true := by decide +kernel
#print axioms leaf00175_raw
theorem leaf00175_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00175=true := by decide +kernel
#print axioms leaf00175_rectangular
def affine00175 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00175 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00175_transform : affine00175=(NestedInteger.clearedAll 3 raw00175 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00175_transform
theorem leaf00175_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00175=true := by decide +kernel
#print axioms leaf00175_sign
theorem leaf00175_log : RationalLog.accepts (235583/1073741824) (-2261460553/536870912) 13 8=true := by decide +kernel
#print axioms leaf00175_log
def leaf00175 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34045360213/100000000000) (235583/1073741824) (-2261460553/536870912) 13 8 ![60,0,4] ![(121/32000),0,0] ![(3/32000),1,(1/16)] affine00175
theorem leaf00175_checked : FastNestedCellData.accepts 1 2 4 leaf00175=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34045360213/100000000000) (235583/1073741824) (-2261460553/536870912) 13 8 ![60,0,4] ![(121/32000),0,0] ![(3/32000),1,(1/16)] 3925162792165404424408976588800000000000 1154392608959767623109301197915291648 3390748700373480824740249600000000000 raw00175 affine00175
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00175_raw leaf00175_rectangular
    leaf00175_transform leaf00175_sign leaf00175_log
#print axioms leaf00175_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
