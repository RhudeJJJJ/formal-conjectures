/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00803 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1286926461286817544582201344000000000000 744162236882187667804173624657794039808 2604196023271360838680707072000000000000))
theorem leaf00803_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1286926461286817544582201344000000000000 744162236882187667804173624657794039808 2604196023271360838680707072000000000000 raw00803=true := by decide +kernel
#print axioms leaf00803_raw
theorem leaf00803_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00803=true := by decide +kernel
#print axioms leaf00803_rectangular
def affine00803 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00803 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00803_transform : affine00803=(NestedInteger.clearedAll 3 raw00803 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00803_transform
theorem leaf00803_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00803=true := by decide +kernel
#print axioms leaf00803_sign
theorem leaf00803_log : RationalLog.accepts (965796249/2147483648) (-429013107/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00803_log
def leaf00803 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8929846177/31250000000) (965796249/2147483648) (-429013107/1073741824) 2 8 ![60,0,4] ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)] affine00803
theorem leaf00803_checked : FastNestedCellData.accepts 1 2 4 leaf00803=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8929846177/31250000000) (965796249/2147483648) (-429013107/1073741824) 2 8 ![60,0,4] ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)] 1286926461286817544582201344000000000000 744162236882187667804173624657794039808 2604196023271360838680707072000000000000 raw00803 affine00803
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00803_raw leaf00803_rectangular
    leaf00803_transform leaf00803_sign leaf00803_log
#print axioms leaf00803_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
