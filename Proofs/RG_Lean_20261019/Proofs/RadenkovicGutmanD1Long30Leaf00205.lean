/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00205 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 107672959818465758049992704000000000000 45521624316485965761455343588605952 119001076648370113609728000000000000))
theorem leaf00205_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 107672959818465758049992704000000000000 45521624316485965761455343588605952 119001076648370113609728000000000000 raw00205=true := by decide +kernel
#print axioms leaf00205_raw
theorem leaf00205_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00205=true := by decide +kernel
#print axioms leaf00205_rectangular
def affine00205 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00205 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00205_transform : affine00205=(NestedInteger.clearedAll 3 raw00205 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00205_transform
theorem leaf00205_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00205=true := by decide +kernel
#print axioms leaf00205_sign
theorem leaf00205_log : RationalLog.accepts (1313397/4294967296) (-17378688603/4294967296) 12 8=true := by decide +kernel
#print axioms leaf00205_log
def leaf00205 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1494262489/3906250000) (1313397/4294967296) (-17378688603/4294967296) 12 8 ![60,0,4] ![(139/32000),0,0] ![(3/32000),1,(1/16)] affine00205
theorem leaf00205_checked : FastNestedCellData.accepts 1 2 4 leaf00205=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1494262489/3906250000) (1313397/4294967296) (-17378688603/4294967296) 12 8 ![60,0,4] ![(139/32000),0,0] ![(3/32000),1,(1/16)] 107672959818465758049992704000000000000 45521624316485965761455343588605952 119001076648370113609728000000000000 raw00205 affine00205
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00205_raw leaf00205_rectangular
    leaf00205_transform leaf00205_sign leaf00205_log
#print axioms leaf00205_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
