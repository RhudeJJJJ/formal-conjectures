/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00281 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 15299006422222897507811196928000000000000 10410960775888398753425546925436217327616 49035131068646051986110676992000000000000))
theorem leaf00281_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 15299006422222897507811196928000000000000 10410960775888398753425546925436217327616 49035131068646051986110676992000000000000 raw00281=true := by decide +kernel
#print axioms leaf00281_raw
theorem leaf00281_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00281=true := by decide +kernel
#print axioms leaf00281_rectangular
def affine00281 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00281 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00281_transform : affine00281=(NestedInteger.clearedAll 3 raw00281 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00281_transform
theorem leaf00281_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00281=true := by decide +kernel
#print axioms leaf00281_sign
theorem leaf00281_log : RationalLog.accepts (301357143/536870912) (-1240089369/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00281_log
def leaf00281 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (106158182399/500000000000) (301357143/536870912) (-1240089369/4294967296) 1 8 ![52,0,4] ![(41/640),0,(1/2)] ![(1/640),1,(1/2)] affine00281
theorem leaf00281_checked : FastNestedCellData.accepts 1 0 4 leaf00281=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (106158182399/500000000000) (301357143/536870912) (-1240089369/4294967296) 1 8 ![52,0,4] ![(41/640),0,(1/2)] ![(1/640),1,(1/2)] 15299006422222897507811196928000000000000 10410960775888398753425546925436217327616 49035131068646051986110676992000000000000 raw00281 affine00281
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00281_raw leaf00281_rectangular
    leaf00281_transform leaf00281_sign leaf00281_log
#print axioms leaf00281_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
