/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00415 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 429552143519825497715124469760000000000 1545914573048285940432884099652255744 2260015656953728900131717120000000000))
theorem leaf00415_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 429552143519825497715124469760000000000 1545914573048285940432884099652255744 2260015656953728900131717120000000000 raw00415=true := by decide +kernel
#print axioms leaf00415_raw
theorem leaf00415_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00415=true := by decide +kernel
#print axioms leaf00415_rectangular
def affine00415 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00415 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00415_transform : affine00415=(NestedInteger.clearedAll 3 raw00415 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00415_transform
theorem leaf00415_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00415=true := by decide +kernel
#print axioms leaf00415_sign
theorem leaf00415_log : RationalLog.accepts (9178677/4294967296) (-6601704349/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00415_log
def leaf00415 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27361130323/40000000000) (9178677/4294967296) (-6601704349/2147483648) 9 8 ![60,0,4] ![(67/6400),0,0] ![(1/6400),1,(1/16)] affine00415
theorem leaf00415_checked : FastNestedCellData.accepts 1 2 4 leaf00415=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27361130323/40000000000) (9178677/4294967296) (-6601704349/2147483648) 9 8 ![60,0,4] ![(67/6400),0,0] ![(1/6400),1,(1/16)] 429552143519825497715124469760000000000 1545914573048285940432884099652255744 2260015656953728900131717120000000000 raw00415 affine00415
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00415_raw leaf00415_rectangular
    leaf00415_transform leaf00415_sign leaf00415_log
#print axioms leaf00415_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
