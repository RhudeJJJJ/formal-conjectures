/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00230 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 479140012710079130259175768064000000000000 263809398166753054752514896028911009792 634786325908200686855651328000000000000))
theorem leaf00230_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 479140012710079130259175768064000000000000 263809398166753054752514896028911009792 634786325908200686855651328000000000000 raw00230=true := by decide +kernel
#print axioms leaf00230_raw
theorem leaf00230_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00230=true := by decide +kernel
#print axioms leaf00230_rectangular
def affine00230 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00230 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/16000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00230_transform : affine00230=(NestedInteger.clearedAll 3 raw00230 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/16000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00230_transform
theorem leaf00230_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00230=true := by decide +kernel
#print axioms leaf00230_sign
theorem leaf00230_log : RationalLog.accepts (1670517/4294967296) (-4215545973/1073741824) 12 8=true := by decide +kernel
#print axioms leaf00230_log
def leaf00230 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (103896928541/250000000000) (1670517/4294967296) (-4215545973/1073741824) 12 8 ![60,0,4] ![(77/16000),0,0] ![(3/32000),1,(1/16)] affine00230
theorem leaf00230_checked : FastNestedCellData.accepts 1 2 4 leaf00230=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (103896928541/250000000000) (1670517/4294967296) (-4215545973/1073741824) 12 8 ![60,0,4] ![(77/16000),0,0] ![(3/32000),1,(1/16)] 479140012710079130259175768064000000000000 263809398166753054752514896028911009792 634786325908200686855651328000000000000 raw00230 affine00230
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00230_raw leaf00230_rectangular
    leaf00230_transform leaf00230_sign leaf00230_log
#print axioms leaf00230_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
