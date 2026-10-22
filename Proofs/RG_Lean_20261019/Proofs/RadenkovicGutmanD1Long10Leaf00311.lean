/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00311 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8116994919337943344246926868480000000000 5294779660044585507097634725835776720896 19252730112289749892435405701120000000000))
theorem leaf00311_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8116994919337943344246926868480000000000 5294779660044585507097634725835776720896 19252730112289749892435405701120000000000 raw00311=true := by decide +kernel
#print axioms leaf00311_raw
theorem leaf00311_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00311=true := by decide +kernel
#print axioms leaf00311_rectangular
def affine00311 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00311 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00311_transform : affine00311=(NestedInteger.clearedAll 3 raw00311 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00311_transform
theorem leaf00311_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00311=true := by decide +kernel
#print axioms leaf00311_sign
theorem leaf00311_log : RationalLog.accepts (2197340499/4294967296) (-1439235365/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00311_log
def leaf00311 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (11000579407/40000000000) (2197340499/4294967296) (-1439235365/4294967296) 1 8 ![52,0,4] ![(29/320),0,(1/2)] ![(1/320),1,(1/2)] affine00311
theorem leaf00311_checked : FastNestedCellData.accepts 1 0 4 leaf00311=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (11000579407/40000000000) (2197340499/4294967296) (-1439235365/4294967296) 1 8 ![52,0,4] ![(29/320),0,(1/2)] ![(1/320),1,(1/2)] 8116994919337943344246926868480000000000 5294779660044585507097634725835776720896 19252730112289749892435405701120000000000 raw00311 affine00311
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00311_raw leaf00311_rectangular
    leaf00311_transform leaf00311_sign leaf00311_log
#print axioms leaf00311_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
