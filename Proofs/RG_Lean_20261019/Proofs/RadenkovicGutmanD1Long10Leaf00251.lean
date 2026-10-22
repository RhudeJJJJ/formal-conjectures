/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00251 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 257774809613505539958663806976000000000000 184674337838713439903356659200551494352896 1101297243448091428376205590528000000000000))
theorem leaf00251_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 257774809613505539958663806976000000000000 184674337838713439903356659200551494352896 1101297243448091428376205590528000000000000 raw00251=true := by decide +kernel
#print axioms leaf00251_raw
theorem leaf00251_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00251=true := by decide +kernel
#print axioms leaf00251_rectangular
def affine00251 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00251 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)]))
theorem leaf00251_transform : affine00251=(NestedInteger.clearedAll 3 raw00251 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00251_transform
theorem leaf00251_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00251=true := by decide +kernel
#print axioms leaf00251_sign
theorem leaf00251_log : RationalLog.accepts (1317556119/2147483648) (-524542403/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00251_log
def leaf00251 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (167688005157/1000000000000) (1317556119/2147483648) (-524542403/2147483648) 1 8 ![52,0,4] ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)] affine00251
theorem leaf00251_checked : FastNestedCellData.accepts 1 0 4 leaf00251=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (167688005157/1000000000000) (1317556119/2147483648) (-524542403/2147483648) 1 8 ![52,0,4] ![(77/1600),0,(1/2)] ![(3/1600),1,(1/2)] 257774809613505539958663806976000000000000 184674337838713439903356659200551494352896 1101297243448091428376205590528000000000000 raw00251 affine00251
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00251_raw leaf00251_rectangular
    leaf00251_transform leaf00251_sign leaf00251_log
#print axioms leaf00251_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
