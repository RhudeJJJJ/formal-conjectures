/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00746 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 992338410601537977381071880192000000000000 260060873468554949520882160051675761475584 402859576028417863148147572736000000000000))
theorem leaf00746_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 992338410601537977381071880192000000000000 260060873468554949520882160051675761475584 402859576028417863148147572736000000000000 raw00746=true := by decide +kernel
#print axioms leaf00746_raw
theorem leaf00746_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00746=true := by decide +kernel
#print axioms leaf00746_rectangular
def affine00746 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00746 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00746_transform : affine00746=(NestedInteger.clearedAll 3 raw00746 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00746_transform
theorem leaf00746_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00746=true := by decide +kernel
#print axioms leaf00746_sign
theorem leaf00746_log : RationalLog.accepts (342008859/2147483648) (-1972695067/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00746_log
def leaf00746 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (645537276369/1000000000000) (342008859/2147483648) (-1972695067/2147483648) 3 8 ![60,0,4] ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)] affine00746
theorem leaf00746_checked : FastNestedCellData.accepts 1 2 4 leaf00746=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (645537276369/1000000000000) (342008859/2147483648) (-1972695067/2147483648) 3 8 ![60,0,4] ![(53/1600),0,(1/16)] ![(3/6400),1,(1/16)] 992338410601537977381071880192000000000000 260060873468554949520882160051675761475584 402859576028417863148147572736000000000000 raw00746 affine00746
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00746_raw leaf00746_rectangular
    leaf00746_transform leaf00746_sign leaf00746_log
#print axioms leaf00746_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
