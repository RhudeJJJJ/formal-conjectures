/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00125 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15262287096040877458948148428800000000000 2092661493245723438283406479338766336 7904039618189110842228736000000000000))
theorem leaf00125_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15262287096040877458948148428800000000000 2092661493245723438283406479338766336 7904039618189110842228736000000000000 raw00125=true := by decide +kernel
#print axioms leaf00125_raw
theorem leaf00125_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00125=true := by decide +kernel
#print axioms leaf00125_rectangular
def affine00125 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00125 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00125_transform : affine00125=(NestedInteger.clearedAll 3 raw00125 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00125_transform
theorem leaf00125_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00125=true := by decide +kernel
#print axioms leaf00125_sign
theorem leaf00125_log : RationalLog.accepts (116405/1073741824) (-19605634239/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00125_log
def leaf00125 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (132379238613/500000000000) (116405/1073741824) (-19605634239/4294967296) 14 8 ![60,0,4] ![(91/32000),0,0] ![(3/32000),1,(1/16)] affine00125
theorem leaf00125_checked : FastNestedCellData.accepts 1 2 4 leaf00125=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (132379238613/500000000000) (116405/1073741824) (-19605634239/4294967296) 14 8 ![60,0,4] ![(91/32000),0,0] ![(3/32000),1,(1/16)] 15262287096040877458948148428800000000000 2092661493245723438283406479338766336 7904039618189110842228736000000000000 raw00125 affine00125
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00125_raw leaf00125_rectangular
    leaf00125_transform leaf00125_sign leaf00125_log
#print axioms leaf00125_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
