/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00382 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 865991418115843183066742784000000000000 629081589786379785183920471585706737664 4362062647243759493513740288000000000000))
theorem leaf00382_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 865991418115843183066742784000000000000 629081589786379785183920471585706737664 4362062647243759493513740288000000000000 raw00382=true := by decide +kernel
#print axioms leaf00382_raw
theorem leaf00382_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00382=true := by decide +kernel
#print axioms leaf00382_rectangular
def affine00382 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00382 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00382_transform : affine00382=(NestedInteger.clearedAll 3 raw00382 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00382_transform
theorem leaf00382_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00382=true := by decide +kernel
#print axioms leaf00382_sign
theorem leaf00382_log : RationalLog.accepts (2726748147/4294967296) (-487837647/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00382_log
def leaf00382 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4506766929/31250000000) (2726748147/4294967296) (-487837647/2147483648) 1 8 ![60,0,4] ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)] affine00382
theorem leaf00382_checked : FastNestedCellData.accepts 1 2 4 leaf00382=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4506766929/31250000000) (2726748147/4294967296) (-487837647/2147483648) 1 8 ![60,0,4] ![(3/320),0,(1/8)] ![(1/6400),1,(1/8)] 865991418115843183066742784000000000000 629081589786379785183920471585706737664 4362062647243759493513740288000000000000 raw00382 affine00382
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00382_raw leaf00382_rectangular
    leaf00382_transform leaf00382_sign leaf00382_log
#print axioms leaf00382_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
