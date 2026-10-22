/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00354 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2260435361631334759160348672000000000000 2102020293666336154521753108900999069696 67007678056842536259994779648000000000000))
theorem leaf00354_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2260435361631334759160348672000000000000 2102020293666336154521753108900999069696 67007678056842536259994779648000000000000 raw00354=true := by decide +kernel
#print axioms leaf00354_raw
theorem leaf00354_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00354=true := by decide +kernel
#print axioms leaf00354_rectangular
def affine00354 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00354 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00354_transform : affine00354=(NestedInteger.clearedAll 3 raw00354 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00354_transform
theorem leaf00354_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00354=true := by decide +kernel
#print axioms leaf00354_sign
theorem leaf00354_log : RationalLog.accepts (484061183/536870912) (-222364169/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00354_log
def leaf00354 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15684921151/500000000000) (484061183/536870912) (-222364169/4294967296) 1 8 ![60,0,4] ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00354
theorem leaf00354_checked : FastNestedCellData.accepts 1 2 4 leaf00354=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15684921151/500000000000) (484061183/536870912) (-222364169/4294967296) 1 8 ![60,0,4] ![(27/3200),0,(1/2)] ![(1/6400),1,(1/2)] 2260435361631334759160348672000000000000 2102020293666336154521753108900999069696 67007678056842536259994779648000000000000 raw00354 affine00354
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00354_raw leaf00354_rectangular
    leaf00354_transform leaf00354_sign leaf00354_log
#print axioms leaf00354_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
