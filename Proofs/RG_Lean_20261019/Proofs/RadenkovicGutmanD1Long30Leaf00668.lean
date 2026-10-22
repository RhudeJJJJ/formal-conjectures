/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00668 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 53874987878615368151867588608000000000000 36430383067857158946071075523939232907264 194902002366246971429881905152000000000000))
theorem leaf00668_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 53874987878615368151867588608000000000000 36430383067857158946071075523939232907264 194902002366246971429881905152000000000000 raw00668=true := by decide +kernel
#print axioms leaf00668_raw
theorem leaf00668_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00668=true := by decide +kernel
#print axioms leaf00668_rectangular
def affine00668 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00668 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00668_transform : affine00668=(NestedInteger.clearedAll 3 raw00668 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00668_transform
theorem leaf00668_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00668=true := by decide +kernel
#print axioms leaf00668_sign
theorem leaf00668_log : RationalLog.accepts (611725081/1073741824) (-1208221347/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00668_log
def leaf00668 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (93458206241/500000000000) (611725081/1073741824) (-1208221347/4294967296) 1 8 ![60,0,4] ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)] affine00668
theorem leaf00668_checked : FastNestedCellData.accepts 1 2 4 leaf00668=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (93458206241/500000000000) (611725081/1073741824) (-1208221347/4294967296) 1 8 ![60,0,4] ![(41/1600),0,(1/4)] ![(3/6400),1,(1/4)] 53874987878615368151867588608000000000000 36430383067857158946071075523939232907264 194902002366246971429881905152000000000000 raw00668 affine00668
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00668_raw leaf00668_rectangular
    leaf00668_transform leaf00668_sign leaf00668_log
#print axioms leaf00668_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
