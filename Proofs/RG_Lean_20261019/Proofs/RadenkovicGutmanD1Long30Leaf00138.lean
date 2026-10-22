/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00138 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 270177302659773422396820684800000000000 255677977223676497960651481756072935424 10910488604838877955137260748800000000000))
theorem leaf00138_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 270177302659773422396820684800000000000 255677977223676497960651481756072935424 10910488604838877955137260748800000000000 raw00138=true := by decide +kernel
#print axioms leaf00138_raw
theorem leaf00138_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00138=true := by decide +kernel
#print axioms leaf00138_rectangular
def affine00138 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00138 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00138_transform : affine00138=(NestedInteger.clearedAll 3 raw00138 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00138_transform
theorem leaf00138_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00138=true := by decide +kernel
#print axioms leaf00138_sign
theorem leaf00138_log : RationalLog.accepts (3971407201/4294967296) (-168198365/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00138_log
def leaf00138 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (585853637/25000000000) (3971407201/4294967296) (-168198365/4294967296) 1 8 ![60,0,4] ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00138
theorem leaf00138_checked : FastNestedCellData.accepts 1 2 4 leaf00138=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (585853637/25000000000) (3971407201/4294967296) (-168198365/4294967296) 1 8 ![60,0,4] ![(97/32000),0,(1/4)] ![(3/32000),1,(1/4)] 270177302659773422396820684800000000000 255677977223676497960651481756072935424 10910488604838877955137260748800000000000 raw00138 affine00138
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00138_raw leaf00138_rectangular
    leaf00138_transform leaf00138_sign leaf00138_log
#print axioms leaf00138_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
