/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00444 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7684303615533834701078999859200000000000 6987122434930582294096619569876876394496 167731086403572178059715726540800000000000))
theorem leaf00444_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7684303615533834701078999859200000000000 6987122434930582294096619569876876394496 167731086403572178059715726540800000000000 raw00444=true := by decide +kernel
#print axioms leaf00444_raw
theorem leaf00444_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00444=true := by decide +kernel
#print axioms leaf00444_rectangular
def affine00444 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00444 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00444_transform : affine00444=(NestedInteger.clearedAll 3 raw00444 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00444_transform
theorem leaf00444_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00444=true := by decide +kernel
#print axioms leaf00444_sign
theorem leaf00444_log : RationalLog.accepts (3749117829/4294967296) (-291893259/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00444_log
def leaf00444 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4165669337/100000000000) (3749117829/4294967296) (-291893259/4294967296) 1 8 ![60,0,4] ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)] affine00444
theorem leaf00444_checked : FastNestedCellData.accepts 1 2 4 leaf00444=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4165669337/100000000000) (3749117829/4294967296) (-291893259/4294967296) 1 8 ![60,0,4] ![(9/800),0,(1/2)] ![(1/6400),1,(1/2)] 7684303615533834701078999859200000000000 6987122434930582294096619569876876394496 167731086403572178059715726540800000000000 raw00444 affine00444
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00444_raw leaf00444_rectangular
    leaf00444_transform leaf00444_sign leaf00444_log
#print axioms leaf00444_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
