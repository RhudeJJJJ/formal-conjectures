/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00856 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3333593031869083731969513095168000000000000 864350691607833409457187169127857523785728 1195741040192584089426758467584000000000000))
theorem leaf00856_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3333593031869083731969513095168000000000000 864350691607833409457187169127857523785728 1195741040192584089426758467584000000000000 raw00856=true := by decide +kernel
#print axioms leaf00856_raw
theorem leaf00856_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00856=true := by decide +kernel
#print axioms leaf00856_rectangular
def affine00856 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00856 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00856_transform : affine00856=(NestedInteger.clearedAll 3 raw00856 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00856_transform
theorem leaf00856_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00856=true := by decide +kernel
#print axioms leaf00856_sign
theorem leaf00856_log : RationalLog.accepts (323189949/2147483648) (-1016732501/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00856_log
def leaf00856 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (722857761467/1000000000000) (323189949/2147483648) (-1016732501/1073741824) 3 8 ![60,0,4] ![(7/128),0,(1/16)] ![(1/640),1,(1/16)] affine00856
theorem leaf00856_checked : FastNestedCellData.accepts 1 2 4 leaf00856=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (722857761467/1000000000000) (323189949/2147483648) (-1016732501/1073741824) 3 8 ![60,0,4] ![(7/128),0,(1/16)] ![(1/640),1,(1/16)] 3333593031869083731969513095168000000000000 864350691607833409457187169127857523785728 1195741040192584089426758467584000000000000 raw00856 affine00856
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00856_raw leaf00856_rectangular
    leaf00856_transform leaf00856_sign leaf00856_log
#print axioms leaf00856_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
