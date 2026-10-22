/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00435 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16855374369125632969986277376000000000000 69138322207540208136948830722068578304 98523296783407022077902848000000000000))
theorem leaf00435_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16855374369125632969986277376000000000000 69138322207540208136948830722068578304 98523296783407022077902848000000000000 raw00435=true := by decide +kernel
#print axioms leaf00435_raw
theorem leaf00435_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00435=true := by decide +kernel
#print axioms leaf00435_rectangular
def affine00435 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00435 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00435_transform : affine00435=(NestedInteger.clearedAll 3 raw00435 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00435_transform
theorem leaf00435_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00435=true := by decide +kernel
#print axioms leaf00435_sign
theorem leaf00435_log : RationalLog.accepts (2588127/1073741824) (-12944968205/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00435_log
def leaf00435 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (175436481687/250000000000) (2588127/1073741824) (-12944968205/4294967296) 9 8 ![60,0,4] ![(71/6400),0,0] ![(1/6400),1,(1/16)] affine00435
theorem leaf00435_checked : FastNestedCellData.accepts 1 2 4 leaf00435=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (175436481687/250000000000) (2588127/1073741824) (-12944968205/4294967296) 9 8 ![60,0,4] ![(71/6400),0,0] ![(1/6400),1,(1/16)] 16855374369125632969986277376000000000000 69138322207540208136948830722068578304 98523296783407022077902848000000000000 raw00435 affine00435
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00435_raw leaf00435_rectangular
    leaf00435_transform leaf00435_sign leaf00435_log
#print axioms leaf00435_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
