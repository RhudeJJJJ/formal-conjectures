/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00238 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 44463722157543017484415664128000000000 40758924580758293443332625851920416768 1082222596187506621716096876544000000000))
theorem leaf00238_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 44463722157543017484415664128000000000 40758924580758293443332625851920416768 1082222596187506621716096876544000000000 raw00238=true := by decide +kernel
#print axioms leaf00238_raw
theorem leaf00238_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00238=true := by decide +kernel
#print axioms leaf00238_rectangular
def affine00238 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00238 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00238_transform : affine00238=(NestedInteger.clearedAll 3 raw00238 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00238_transform
theorem leaf00238_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00238=true := by decide +kernel
#print axioms leaf00238_sign
theorem leaf00238_log : RationalLog.accepts (3794204633/4294967296) (-133110863/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00238_log
def leaf00238 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (301297901/8000000000) (3794204633/4294967296) (-133110863/2147483648) 1 8 ![60,0,4] ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00238
theorem leaf00238_checked : FastNestedCellData.accepts 1 2 4 leaf00238=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (301297901/8000000000) (3794204633/4294967296) (-133110863/2147483648) 1 8 ![60,0,4] ![(157/32000),0,(1/4)] ![(3/32000),1,(1/4)] 44463722157543017484415664128000000000 40758924580758293443332625851920416768 1082222596187506621716096876544000000000 raw00238 affine00238
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00238_raw leaf00238_rectangular
    leaf00238_transform leaf00238_sign leaf00238_log
#print axioms leaf00238_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
