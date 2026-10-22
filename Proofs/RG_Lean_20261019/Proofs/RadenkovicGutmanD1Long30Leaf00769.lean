/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00769 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 581038935287618129386012672000000000000 444499326301272842617464242383626436608 3445288910468489231984492544000000000000))
theorem leaf00769_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 581038935287618129386012672000000000000 444499326301272842617464242383626436608 3445288910468489231984492544000000000000 raw00769=true := by decide +kernel
#print axioms leaf00769_raw
theorem leaf00769_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00769=true := by decide +kernel
#print axioms leaf00769_rectangular
def affine00769 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00769 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00769_transform : affine00769=(NestedInteger.clearedAll 3 raw00769 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00769_transform
theorem leaf00769_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00769=true := by decide +kernel
#print axioms leaf00769_sign
theorem leaf00769_log : RationalLog.accepts (2910217317/4294967296) (-835835425/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00769_log
def leaf00769 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2015883763/15625000000) (2910217317/4294967296) (-835835425/4294967296) 1 8 ![60,0,4] ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)] affine00769
theorem leaf00769_checked : FastNestedCellData.accepts 1 2 4 leaf00769=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2015883763/15625000000) (2910217317/4294967296) (-835835425/4294967296) 1 8 ![60,0,4] ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)] 581038935287618129386012672000000000000 444499326301272842617464242383626436608 3445288910468489231984492544000000000000 raw00769 affine00769
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00769_raw leaf00769_rectangular
    leaf00769_transform leaf00769_sign leaf00769_log
#print axioms leaf00769_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
