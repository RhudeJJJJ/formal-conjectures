/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00858 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1575072070382548104642585165824000000000000 854286515190113902380889073479138324512768 2501283117080759042959975907328000000000000))
theorem leaf00858_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1575072070382548104642585165824000000000000 854286515190113902380889073479138324512768 2501283117080759042959975907328000000000000 raw00858=true := by decide +kernel
#print axioms leaf00858_raw
theorem leaf00858_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00858=true := by decide +kernel
#print axioms leaf00858_rectangular
def affine00858 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00858 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00858_transform : affine00858=(NestedInteger.clearedAll 3 raw00858 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00858_transform
theorem leaf00858_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00858=true := by decide +kernel
#print axioms leaf00858_sign
theorem leaf00858_log : RationalLog.accepts (1736439187/4294967296) (-1944777087/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00858_log
def leaf00858 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (170769656053/500000000000) (1736439187/4294967296) (-1944777087/4294967296) 2 8 ![60,0,4] ![(7/128),0,(1/4)] ![(1/640),1,(1/4)] affine00858
theorem leaf00858_checked : FastNestedCellData.accepts 1 2 4 leaf00858=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (170769656053/500000000000) (1736439187/4294967296) (-1944777087/4294967296) 2 8 ![60,0,4] ![(7/128),0,(1/4)] ![(1/640),1,(1/4)] 1575072070382548104642585165824000000000000 854286515190113902380889073479138324512768 2501283117080759042959975907328000000000000 raw00858 affine00858
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00858_raw leaf00858_rectangular
    leaf00858_transform leaf00858_sign leaf00858_log
#print axioms leaf00858_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
