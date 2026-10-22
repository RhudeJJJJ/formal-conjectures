/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00134 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1102858208187169588001539883008000000000000 960347491684344152092608234814525440786432 16063066194202447199397702795264000000000000))
theorem leaf00134_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1102858208187169588001539883008000000000000 960347491684344152092608234814525440786432 16063066194202447199397702795264000000000000 raw00134=true := by decide +kernel
#print axioms leaf00134_raw
theorem leaf00134_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00134=true := by decide +kernel
#print axioms leaf00134_rectangular
def affine00134 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00134 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00134_transform : affine00134=(NestedInteger.clearedAll 3 raw00134 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00134_transform
theorem leaf00134_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00134=true := by decide +kernel
#print axioms leaf00134_sign
theorem leaf00134_log : RationalLog.accepts (3528989643/4294967296) (-421835255/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00134_log
def leaf00134 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (59786063263/1000000000000) (3528989643/4294967296) (-421835255/4294967296) 1 8 ![52,0,4] ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)] affine00134
theorem leaf00134_checked : FastNestedCellData.accepts 1 0 4 leaf00134=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (59786063263/1000000000000) (3528989643/4294967296) (-421835255/4294967296) 1 8 ![52,0,4] ![(13/800),0,(1/2)] ![(1/1600),1,(1/2)] 1102858208187169588001539883008000000000000 960347491684344152092608234814525440786432 16063066194202447199397702795264000000000000 raw00134 affine00134
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00134_raw leaf00134_rectangular
    leaf00134_transform leaf00134_sign leaf00134_log
#print axioms leaf00134_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
