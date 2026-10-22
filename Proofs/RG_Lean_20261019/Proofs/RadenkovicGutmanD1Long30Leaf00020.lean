/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00020 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 559573234477273038989440319488000000000000 7663237114302887172203337393387864064 63156064798091790895808512000000000000))
theorem leaf00020_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 559573234477273038989440319488000000000000 7663237114302887172203337393387864064 63156064798091790895808512000000000000 raw00020=true := by decide +kernel
#print axioms leaf00020_raw
theorem leaf00020_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00020=true := by decide +kernel
#print axioms leaf00020_rectangular
def affine00020 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00020 (IntegerComputedClassCell.leftNumerator ![(1/800),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/800),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00020_transform : affine00020=(NestedInteger.clearedAll 3 raw00020 (IntegerComputedClassCell.leftNumerator ![(1/800),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/800),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00020_transform
theorem leaf00020_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00020=true := by decide +kernel
#print axioms leaf00020_sign
theorem leaf00020_log : RationalLog.accepts (26227/2147483648) (-12147260779/2147483648) 17 8=true := by decide +kernel
#print axioms leaf00020_log
def leaf00020 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (121338103297/1000000000000) (26227/2147483648) (-12147260779/2147483648) 17 8 ![60,0,4] ![(1/800),0,0] ![(1/16000),1,(1/16)] affine00020
theorem leaf00020_checked : FastNestedCellData.accepts 1 2 4 leaf00020=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (121338103297/1000000000000) (26227/2147483648) (-12147260779/2147483648) 17 8 ![60,0,4] ![(1/800),0,0] ![(1/16000),1,(1/16)] 559573234477273038989440319488000000000000 7663237114302887172203337393387864064 63156064798091790895808512000000000000 raw00020 affine00020
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00020_raw leaf00020_rectangular
    leaf00020_transform leaf00020_sign leaf00020_log
#print axioms leaf00020_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
