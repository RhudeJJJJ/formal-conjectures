/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00356 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 21297315568244461014750079221760000000000 12015579842361817986653268754250361470976 46254828175990068955154743296000000000000))
theorem leaf00356_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 21297315568244461014750079221760000000000 12015579842361817986653268754250361470976 46254828175990068955154743296000000000000 raw00356=true := by decide +kernel
#print axioms leaf00356_raw
theorem leaf00356_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00356=true := by decide +kernel
#print axioms leaf00356_rectangular
def affine00356 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00356 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00356_transform : affine00356=(NestedInteger.clearedAll 3 raw00356 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00356_transform
theorem leaf00356_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00356=true := by decide +kernel
#print axioms leaf00356_sign
theorem leaf00356_log : RationalLog.accepts (1923484725/4294967296) (-862542683/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00356_log
def leaf00356 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (259769202831/1000000000000) (1923484725/4294967296) (-862542683/2147483648) 2 8 ![60,0,4] ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)] affine00356
theorem leaf00356_checked : FastNestedCellData.accepts 1 2 4 leaf00356=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (259769202831/1000000000000) (1923484725/4294967296) (-862542683/2147483648) 2 8 ![60,0,4] ![(11/1280),0,(1/16)] ![(1/6400),1,(1/16)] 21297315568244461014750079221760000000000 12015579842361817986653268754250361470976 46254828175990068955154743296000000000000 raw00356 affine00356
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00356_raw leaf00356_rectangular
    leaf00356_transform leaf00356_sign leaf00356_log
#print axioms leaf00356_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
