/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00280 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 374312190496395511566045492019200000000000 398377124716486450069676414090323427328 785308205401454935453309337600000000000))
theorem leaf00280_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 374312190496395511566045492019200000000000 398377124716486450069676414090323427328 785308205401454935453309337600000000000 raw00280=true := by decide +kernel
#print axioms leaf00280_raw
theorem leaf00280_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00280=true := by decide +kernel
#print axioms leaf00280_rectangular
def affine00280 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00280 (IntegerComputedClassCell.leftNumerator ![(1/160),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/160),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00280_transform : affine00280=(NestedInteger.clearedAll 3 raw00280 (IntegerComputedClassCell.leftNumerator ![(1/160),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/160),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00280_transform
theorem leaf00280_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00280=true := by decide +kernel
#print axioms leaf00280_sign
theorem leaf00280_log : RationalLog.accepts (3032663/4294967296) (-1947702785/536870912) 11 8=true := by decide +kernel
#print axioms leaf00280_log
def leaf00280 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (101457522531/200000000000) (3032663/4294967296) (-1947702785/536870912) 11 8 ![60,0,4] ![(1/160),0,0] ![(1/6400),1,(1/16)] affine00280
theorem leaf00280_checked : FastNestedCellData.accepts 1 2 4 leaf00280=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (101457522531/200000000000) (3032663/4294967296) (-1947702785/536870912) 11 8 ![60,0,4] ![(1/160),0,0] ![(1/6400),1,(1/16)] 374312190496395511566045492019200000000000 398377124716486450069676414090323427328 785308205401454935453309337600000000000 raw00280 affine00280
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00280_raw leaf00280_rectangular
    leaf00280_transform leaf00280_sign leaf00280_log
#print axioms leaf00280_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
