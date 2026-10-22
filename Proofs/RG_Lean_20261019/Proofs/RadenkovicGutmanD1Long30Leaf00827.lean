/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00827 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 36849589827568949702638436352000000000000 14339868929029747335802974114753055555584 28040921450693142460562931712000000000000))
theorem leaf00827_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 36849589827568949702638436352000000000000 14339868929029747335802974114753055555584 28040921450693142460562931712000000000000 raw00827=true := by decide +kernel
#print axioms leaf00827_raw
theorem leaf00827_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00827=true := by decide +kernel
#print axioms leaf00827_rectangular
def affine00827 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00827 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00827_transform : affine00827=(NestedInteger.clearedAll 3 raw00827 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00827_transform
theorem leaf00827_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00827=true := by decide +kernel
#print axioms leaf00827_sign
theorem leaf00827_log : RationalLog.accepts (1105848451/4294967296) (-2913772611/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00827_log
def leaf00827 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (31961924277/62500000000) (1105848451/4294967296) (-2913772611/4294967296) 2 8 ![60,0,4] ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)] affine00827
theorem leaf00827_checked : FastNestedCellData.accepts 1 2 4 leaf00827=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (31961924277/62500000000) (1105848451/4294967296) (-2913772611/4294967296) 2 8 ![60,0,4] ![(151/3200),0,(1/8)] ![(3/3200),1,(1/8)] 36849589827568949702638436352000000000000 14339868929029747335802974114753055555584 28040921450693142460562931712000000000000 raw00827 affine00827
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00827_raw leaf00827_rectangular
    leaf00827_transform leaf00827_sign leaf00827_log
#print axioms leaf00827_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
