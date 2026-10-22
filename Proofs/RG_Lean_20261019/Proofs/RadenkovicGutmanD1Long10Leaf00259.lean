/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00259 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 6278079282626602846571733188608000000000000 3368455055470674069034493699539153488707584 9897458368200782503111051706368000000000000))
theorem leaf00259_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 6278079282626602846571733188608000000000000 3368455055470674069034493699539153488707584 9897458368200782503111051706368000000000000 raw00259=true := by decide +kernel
#print axioms leaf00259_raw
theorem leaf00259_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00259=true := by decide +kernel
#print axioms leaf00259_rectangular
def affine00259 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00259 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00259_transform : affine00259=(NestedInteger.clearedAll 3 raw00259 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00259_transform
theorem leaf00259_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00259=true := by decide +kernel
#print axioms leaf00259_sign
theorem leaf00259_log : RationalLog.accepts (1719294791/4294967296) (-61440163/134217728) 2 8=true := by decide +kernel
#print axioms leaf00259_log
def leaf00259 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (340335359863/1000000000000) (1719294791/4294967296) (-61440163/134217728) 2 8 ![52,0,4] ![(17/320),0,(1/4)] ![(1/640),1,(1/4)] affine00259
theorem leaf00259_checked : FastNestedCellData.accepts 1 0 4 leaf00259=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (340335359863/1000000000000) (1719294791/4294967296) (-61440163/134217728) 2 8 ![52,0,4] ![(17/320),0,(1/4)] ![(1/640),1,(1/4)] 6278079282626602846571733188608000000000000 3368455055470674069034493699539153488707584 9897458368200782503111051706368000000000000 raw00259 affine00259
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00259_raw leaf00259_rectangular
    leaf00259_transform leaf00259_sign leaf00259_log
#print axioms leaf00259_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
