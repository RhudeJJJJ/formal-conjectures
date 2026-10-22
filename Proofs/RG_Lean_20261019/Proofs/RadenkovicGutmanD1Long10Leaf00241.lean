/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00241 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 348838868981842606339263561728000000000000 196037740134550138252347680953414233096192 647909812846618222089065201664000000000000))
theorem leaf00241_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 348838868981842606339263561728000000000000 196037740134550138252347680953414233096192 647909812846618222089065201664000000000000 raw00241=true := by decide +kernel
#print axioms leaf00241_raw
theorem leaf00241_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00241=true := by decide +kernel
#print axioms leaf00241_rectangular
def affine00241 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00241 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00241_transform : affine00241=(NestedInteger.clearedAll 3 raw00241 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00241_transform
theorem leaf00241_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00241=true := by decide +kernel
#print axioms leaf00241_sign
theorem leaf00241_log : RationalLog.accepts (926496499/2147483648) (-1805264531/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00241_log
def leaf00241 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (151284743839/500000000000) (926496499/2147483648) (-1805264531/4294967296) 2 8 ![52,0,4] ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)] affine00241
theorem leaf00241_checked : FastNestedCellData.accepts 1 0 4 leaf00241=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (151284743839/500000000000) (926496499/2147483648) (-1805264531/4294967296) 2 8 ![52,0,4] ![(29/640),0,(1/4)] ![(3/3200),1,(1/4)] 348838868981842606339263561728000000000000 196037740134550138252347680953414233096192 647909812846618222089065201664000000000000 raw00241 affine00241
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00241_raw leaf00241_rectangular
    leaf00241_transform leaf00241_sign leaf00241_log
#print axioms leaf00241_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
