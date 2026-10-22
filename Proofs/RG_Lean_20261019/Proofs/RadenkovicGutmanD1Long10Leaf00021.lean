/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00021 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 114953903628768389962022256640000000000 2833828662664360295062318190952448 45474673272278263917445120000000000))
theorem leaf00021_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 114953903628768389962022256640000000000 2833828662664360295062318190952448 45474673272278263917445120000000000 raw00021=true := by decide +kernel
#print axioms leaf00021_raw
theorem leaf00021_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00021=true := by decide +kernel
#print axioms leaf00021_rectangular
def affine00021 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00021 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/16000),0,0] ![(3/16000),1,(1/4)]))
theorem leaf00021_transform : affine00021=(NestedInteger.clearedAll 3 raw00021 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/16000),0,0] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00021_transform
theorem leaf00021_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00021=true := by decide +kernel
#print axioms leaf00021_sign
theorem leaf00021_log : RationalLog.accepts (24917/1073741824) (-5729008611/1073741824) 16 8=true := by decide +kernel
#print axioms leaf00021_log
def leaf00021 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2492665441/40000000000) (24917/1073741824) (-5729008611/1073741824) 16 8 ![52,0,4] ![(41/16000),0,0] ![(3/16000),1,(1/4)] affine00021
theorem leaf00021_checked : FastNestedCellData.accepts 1 0 4 leaf00021=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2492665441/40000000000) (24917/1073741824) (-5729008611/1073741824) 16 8 ![52,0,4] ![(41/16000),0,0] ![(3/16000),1,(1/4)] 114953903628768389962022256640000000000 2833828662664360295062318190952448 45474673272278263917445120000000000 raw00021 affine00021
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00021_raw leaf00021_rectangular
    leaf00021_transform leaf00021_sign leaf00021_log
#print axioms leaf00021_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
