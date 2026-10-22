/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00887 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 420518544454489786878037223014400000000000 161856843734391645876687341626846278057984 284004766241156815461307278950400000000000))
theorem leaf00887_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 420518544454489786878037223014400000000000 161856843734391645876687341626846278057984 284004766241156815461307278950400000000000 raw00887=true := by decide +kernel
#print axioms leaf00887_raw
theorem leaf00887_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00887=true := by decide +kernel
#print axioms leaf00887_rectangular
def affine00887 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00887 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00887_transform : affine00887=(NestedInteger.clearedAll 3 raw00887 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00887_transform
theorem leaf00887_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00887=true := by decide +kernel
#print axioms leaf00887_sign
theorem leaf00887_log : RationalLog.accepts (1053007161/4294967296) (-188682471/268435456) 3 8=true := by decide +kernel
#print axioms leaf00887_log
def leaf00887 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (113981779867/200000000000) (1053007161/4294967296) (-188682471/268435456) 3 8 ![60,0,4] ![(41/640),0,(1/8)] ![(1/640),1,(1/8)] affine00887
theorem leaf00887_checked : FastNestedCellData.accepts 1 2 4 leaf00887=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (113981779867/200000000000) (1053007161/4294967296) (-188682471/268435456) 3 8 ![60,0,4] ![(41/640),0,(1/8)] ![(1/640),1,(1/8)] 420518544454489786878037223014400000000000 161856843734391645876687341626846278057984 284004766241156815461307278950400000000000 raw00887 affine00887
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00887_raw leaf00887_rectangular
    leaf00887_transform leaf00887_sign leaf00887_log
#print axioms leaf00887_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
