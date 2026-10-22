/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00752 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 488935935634585166007052009472000000000000 211773633201456098026361914444016554868736 499366804589215807675708735488000000000000))
theorem leaf00752_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 488935935634585166007052009472000000000000 211773633201456098026361914444016554868736 499366804589215807675708735488000000000000 raw00752=true := by decide +kernel
#print axioms leaf00752_raw
theorem leaf00752_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00752=true := by decide +kernel
#print axioms leaf00752_rectangular
def affine00752 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00752 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00752_transform : affine00752=(NestedInteger.clearedAll 3 raw00752 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00752_transform
theorem leaf00752_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00752=true := by decide +kernel
#print axioms leaf00752_sign
theorem leaf00752_log : RationalLog.accepts (326575871/1073741824) (-2556026507/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00752_log
def leaf00752 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (424084322897/1000000000000) (326575871/1073741824) (-2556026507/4294967296) 2 8 ![60,0,4] ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)] affine00752
theorem leaf00752_checked : FastNestedCellData.accepts 1 2 4 leaf00752=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (424084322897/1000000000000) (326575871/1073741824) (-2556026507/4294967296) 2 8 ![60,0,4] ![(43/1280),0,(1/8)] ![(3/6400),1,(1/8)] 488935935634585166007052009472000000000000 211773633201456098026361914444016554868736 499366804589215807675708735488000000000000 raw00752 affine00752
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00752_raw leaf00752_rectangular
    leaf00752_transform leaf00752_sign leaf00752_log
#print axioms leaf00752_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
