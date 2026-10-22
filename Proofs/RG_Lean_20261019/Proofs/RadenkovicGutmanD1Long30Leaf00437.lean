/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00437 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 779880258117915554857304981504000000000000 538235360683117844284413134234630410469376 3182761022154582789667449470976000000000000))
theorem leaf00437_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 779880258117915554857304981504000000000000 538235360683117844284413134234630410469376 3182761022154582789667449470976000000000000 raw00437=true := by decide +kernel
#print axioms leaf00437_raw
theorem leaf00437_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00437=true := by decide +kernel
#print axioms leaf00437_rectangular
def affine00437 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00437 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00437_transform : affine00437=(NestedInteger.clearedAll 3 raw00437 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00437_transform
theorem leaf00437_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00437=true := by decide +kernel
#print axioms leaf00437_sign
theorem leaf00437_log : RationalLog.accepts (2535414349/4294967296) (-565955231/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00437_log
def leaf00437 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (84554787013/500000000000) (2535414349/4294967296) (-565955231/2147483648) 1 8 ![60,0,4] ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00437
theorem leaf00437_checked : FastNestedCellData.accepts 1 2 4 leaf00437=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (84554787013/500000000000) (2535414349/4294967296) (-565955231/2147483648) 1 8 ![60,0,4] ![(71/6400),0,(1/8)] ![(1/6400),1,(1/8)] 779880258117915554857304981504000000000000 538235360683117844284413134234630410469376 3182761022154582789667449470976000000000000 raw00437 affine00437
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00437_raw leaf00437_rectangular
    leaf00437_transform leaf00437_sign leaf00437_log
#print axioms leaf00437_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
