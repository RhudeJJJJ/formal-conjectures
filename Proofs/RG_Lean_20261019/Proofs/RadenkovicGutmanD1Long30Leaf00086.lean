/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00086 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 77575505720428263449707937792000000000000 66312951821082557364631576555358622056448 985538250488659337305594527744000000000000))
theorem leaf00086_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 77575505720428263449707937792000000000000 66312951821082557364631576555358622056448 985538250488659337305594527744000000000000 raw00086=true := by decide +kernel
#print axioms leaf00086_raw
theorem leaf00086_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00086=true := by decide +kernel
#print axioms leaf00086_rectangular
def affine00086 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00086 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00086_transform : affine00086=(NestedInteger.clearedAll 3 raw00086 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00086_transform
theorem leaf00086_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00086=true := by decide +kernel
#print axioms leaf00086_sign
theorem leaf00086_log : RationalLog.accepts (859988793/1073741824) (-476710269/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00086_log
def leaf00086 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (67286025467/1000000000000) (859988793/1073741824) (-476710269/4294967296) 1 8 ![60,0,4] ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00086
theorem leaf00086_checked : FastNestedCellData.accepts 1 2 4 leaf00086=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (67286025467/1000000000000) (859988793/1073741824) (-476710269/4294967296) 1 8 ![60,0,4] ![(67/32000),0,(1/16)] ![(3/32000),1,(1/16)] 77575505720428263449707937792000000000000 66312951821082557364631576555358622056448 985538250488659337305594527744000000000000 raw00086 affine00086
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00086_raw leaf00086_rectangular
    leaf00086_transform leaf00086_sign leaf00086_log
#print axioms leaf00086_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
