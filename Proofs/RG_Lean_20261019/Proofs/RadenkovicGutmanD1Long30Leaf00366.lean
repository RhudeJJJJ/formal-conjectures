/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00366 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12367063154154736376056329011200000000000 6855632405038828121162464119905912356864 25564698518721344501090929868800000000000))
theorem leaf00366_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12367063154154736376056329011200000000000 6855632405038828121162464119905912356864 25564698518721344501090929868800000000000 raw00366=true := by decide +kernel
#print axioms leaf00366_raw
theorem leaf00366_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00366=true := by decide +kernel
#print axioms leaf00366_rectangular
def affine00366 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00366 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00366_transform : affine00366=(NestedInteger.clearedAll 3 raw00366 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00366_transform
theorem leaf00366_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00366=true := by decide +kernel
#print axioms leaf00366_sign
theorem leaf00366_log : RationalLog.accepts (1877431229/4294967296) (-888563771/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00366_log
def leaf00366 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13408396739/50000000000) (1877431229/4294967296) (-888563771/2147483648) 2 8 ![60,0,4] ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00366
theorem leaf00366_checked : FastNestedCellData.accepts 1 2 4 leaf00366=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13408396739/50000000000) (1877431229/4294967296) (-888563771/2147483648) 2 8 ![60,0,4] ![(57/6400),0,(1/16)] ![(1/6400),1,(1/16)] 12367063154154736376056329011200000000000 6855632405038828121162464119905912356864 25564698518721344501090929868800000000000 raw00366 affine00366
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00366_raw leaf00366_rectangular
    leaf00366_transform leaf00366_sign leaf00366_log
#print axioms leaf00366_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
