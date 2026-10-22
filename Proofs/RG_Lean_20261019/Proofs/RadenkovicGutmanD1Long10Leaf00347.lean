/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00347 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 410367446850369144050956632064000000000000 284361117289754309031870563666258533810176 798908514097925001025299677184000000000000))
theorem leaf00347_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 410367446850369144050956632064000000000000 284361117289754309031870563666258533810176 798908514097925001025299677184000000000000 raw00347=true := by decide +kernel
#print axioms leaf00347_raw
theorem leaf00347_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00347=true := by decide +kernel
#print axioms leaf00347_rectangular
def affine00347 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00347 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf00347_transform : affine00347=(NestedInteger.clearedAll 3 raw00347 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00347_transform
theorem leaf00347_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00347=true := by decide +kernel
#print axioms leaf00347_sign
theorem leaf00347_log : RationalLog.accepts (1097457363/2147483648) (-1441607407/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00347_log
def leaf00347 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (177968510957/500000000000) (1097457363/2147483648) (-1441607407/4294967296) 1 8 ![52,0,4] ![(3/20),0,(1/2)] ![(1/80),1,(1/2)] affine00347
theorem leaf00347_checked : FastNestedCellData.accepts 1 0 4 leaf00347=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (177968510957/500000000000) (1097457363/2147483648) (-1441607407/4294967296) 1 8 ![52,0,4] ![(3/20),0,(1/2)] ![(1/80),1,(1/2)] 410367446850369144050956632064000000000000 284361117289754309031870563666258533810176 798908514097925001025299677184000000000000 raw00347 affine00347
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00347_raw leaf00347_rectangular
    leaf00347_transform leaf00347_sign leaf00347_log
#print axioms leaf00347_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
