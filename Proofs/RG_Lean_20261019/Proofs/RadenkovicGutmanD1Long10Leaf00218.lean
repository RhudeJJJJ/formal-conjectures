/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00218 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 494231134858903965192818996019200000000000 374133945043700429129924476969225243590656 2792844338096486888484557029376000000000000))
theorem leaf00218_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 494231134858903965192818996019200000000000 374133945043700429129924476969225243590656 2792844338096486888484557029376000000000000 raw00218=true := by decide +kernel
#print axioms leaf00218_raw
theorem leaf00218_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00218=true := by decide +kernel
#print axioms leaf00218_rectangular
def affine00218 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00218 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00218_transform : affine00218=(NestedInteger.clearedAll 3 raw00218 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00218_transform
theorem leaf00218_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00218=true := by decide +kernel
#print axioms leaf00218_sign
theorem leaf00218_log : RationalLog.accepts (2867203505/4294967296) (-867812727/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00218_log
def leaf00218 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (133961617531/1000000000000) (2867203505/4294967296) (-867812727/4294967296) 1 8 ![52,0,4] ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00218
theorem leaf00218_checked : FastNestedCellData.accepts 1 0 4 leaf00218=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (133961617531/1000000000000) (2867203505/4294967296) (-867812727/4294967296) 1 8 ![52,0,4] ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)] 494231134858903965192818996019200000000000 374133945043700429129924476969225243590656 2792844338096486888484557029376000000000000 raw00218 affine00218
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00218_raw leaf00218_rectangular
    leaf00218_transform leaf00218_sign leaf00218_log
#print axioms leaf00218_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
