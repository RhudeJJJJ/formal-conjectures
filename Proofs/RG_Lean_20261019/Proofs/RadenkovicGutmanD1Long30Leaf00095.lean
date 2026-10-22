/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00095 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 997581087806260139633886101504000000000000 74783096403148693718203034449546838016 345712408056483310643183616000000000000))
theorem leaf00095_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 997581087806260139633886101504000000000000 74783096403148693718203034449546838016 345712408056483310643183616000000000000 raw00095=true := by decide +kernel
#print axioms leaf00095_raw
theorem leaf00095_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00095=true := by decide +kernel
#print axioms leaf00095_rectangular
def affine00095 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00095 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00095_transform : affine00095=(NestedInteger.clearedAll 3 raw00095 (IntegerComputedClassCell.leftNumerator ![(73/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00095_transform
theorem leaf00095_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00095=true := by decide +kernel
#print axioms leaf00095_sign
theorem leaf00095_log : RationalLog.accepts (264709/4294967296) (-20818401451/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00095_log
def leaf00095 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (108157958263/500000000000) (264709/4294967296) (-20818401451/4294967296) 14 8 ![60,0,4] ![(73/32000),0,0] ![(3/32000),1,(1/16)] affine00095
theorem leaf00095_checked : FastNestedCellData.accepts 1 2 4 leaf00095=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (108157958263/500000000000) (264709/4294967296) (-20818401451/4294967296) 14 8 ![60,0,4] ![(73/32000),0,0] ![(3/32000),1,(1/16)] 997581087806260139633886101504000000000000 74783096403148693718203034449546838016 345712408056483310643183616000000000000 raw00095 affine00095
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00095_raw leaf00095_rectangular
    leaf00095_transform leaf00095_sign leaf00095_log
#print axioms leaf00095_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
