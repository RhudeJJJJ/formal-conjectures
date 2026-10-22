/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00493 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 449493548124683972066165129216000000000000 361344184933790279635282528339935463735296 3707296650756287496513518567424000000000000))
theorem leaf00493_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 449493548124683972066165129216000000000000 361344184933790279635282528339935463735296 3707296650756287496513518567424000000000000 raw00493=true := by decide +kernel
#print axioms leaf00493_raw
theorem leaf00493_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00493=true := by decide +kernel
#print axioms leaf00493_rectangular
def affine00493 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00493 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00493_transform : affine00493=(NestedInteger.clearedAll 3 raw00493 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00493_transform
theorem leaf00493_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00493=true := by decide +kernel
#print axioms leaf00493_sign
theorem leaf00493_log : RationalLog.accepts (1573024397/2147483648) (-668504451/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00493_log
def leaf00493 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (97468376279/1000000000000) (1573024397/2147483648) (-668504451/4294967296) 1 8 ![60,0,4] ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00493
theorem leaf00493_checked : FastNestedCellData.accepts 1 2 4 leaf00493=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (97468376279/1000000000000) (1573024397/2147483648) (-668504451/4294967296) 1 8 ![60,0,4] ![(41/3200),0,(1/4)] ![(1/3200),1,(1/4)] 449493548124683972066165129216000000000000 361344184933790279635282528339935463735296 3707296650756287496513518567424000000000000 raw00493 affine00493
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00493_raw leaf00493_rectangular
    leaf00493_transform leaf00493_sign leaf00493_log
#print axioms leaf00493_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
