/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00699 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 118953547332265928470460104704000000000000 95439962770253364103885633023730199298048 925023153528564312895611994112000000000000))
theorem leaf00699_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 118953547332265928470460104704000000000000 95439962770253364103885633023730199298048 925023153528564312895611994112000000000000 raw00699=true := by decide +kernel
#print axioms leaf00699_raw
theorem leaf00699_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00699=true := by decide +kernel
#print axioms leaf00699_rectangular
def affine00699 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00699 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00699_transform : affine00699=(NestedInteger.clearedAll 3 raw00699 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00699_transform
theorem leaf00699_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00699=true := by decide +kernel
#print axioms leaf00699_sign
theorem leaf00699_log : RationalLog.accepts (1561845319/2147483648) (-683820551/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00699_log
def leaf00699 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (51587877777/500000000000) (1561845319/2147483648) (-683820551/4294967296) 1 8 ![60,0,4] ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00699
theorem leaf00699_checked : FastNestedCellData.accepts 1 2 4 leaf00699=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (51587877777/500000000000) (1561845319/2147483648) (-683820551/4294967296) 1 8 ![60,0,4] ![(91/3200),0,(1/2)] ![(3/6400),1,(1/2)] 118953547332265928470460104704000000000000 95439962770253364103885633023730199298048 925023153528564312895611994112000000000000 raw00699 affine00699
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00699_raw leaf00699_rectangular
    leaf00699_transform leaf00699_sign leaf00699_log
#print axioms leaf00699_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
