/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00134 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 203211251601643200090543751168000000000000 197930595748660102226958521231642359496704 17967386231594238661898165813248000000000000))
theorem leaf00134_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 203211251601643200090543751168000000000000 197930595748660102226958521231642359496704 17967386231594238661898165813248000000000000 raw00134=true := by decide +kernel
#print axioms leaf00134_raw
theorem leaf00134_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00134=true := by decide +kernel
#print axioms leaf00134_rectangular
def affine00134 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00134 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00134_transform : affine00134=(NestedInteger.clearedAll 3 raw00134 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00134_transform
theorem leaf00134_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00134=true := by decide +kernel
#print axioms leaf00134_sign
theorem leaf00134_log : RationalLog.accepts (4137775931/4294967296) (-5004379/268435456) 1 8=true := by decide +kernel
#print axioms leaf00134_log
def leaf00134 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11016104023/1000000000000) (4137775931/4294967296) (-5004379/268435456) 1 8 ![60,0,4] ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)] affine00134
theorem leaf00134_checked : FastNestedCellData.accepts 1 2 4 leaf00134=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11016104023/1000000000000) (4137775931/4294967296) (-5004379/268435456) 1 8 ![60,0,4] ![(47/16000),0,(1/2)] ![(3/32000),1,(1/2)] 203211251601643200090543751168000000000000 197930595748660102226958521231642359496704 17967386231594238661898165813248000000000000 raw00134 affine00134
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00134_raw leaf00134_rectangular
    leaf00134_transform leaf00134_sign leaf00134_log
#print axioms leaf00134_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
