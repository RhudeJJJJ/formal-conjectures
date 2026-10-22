/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00547 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11105643991790638655423591219200000000000 6624025528925086991107431344811578228736 27506667726816314397109203763200000000000))
theorem leaf00547_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11105643991790638655423591219200000000000 6624025528925086991107431344811578228736 27506667726816314397109203763200000000000 raw00547=true := by decide +kernel
#print axioms leaf00547_raw
theorem leaf00547_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00547=true := by decide +kernel
#print axioms leaf00547_rectangular
def affine00547 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00547 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00547_transform : affine00547=(NestedInteger.clearedAll 3 raw00547 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00547_transform
theorem leaf00547_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00547=true := by decide +kernel
#print axioms leaf00547_sign
theorem leaf00547_log : RationalLog.accepts (516144129/1073741824) (-393268061/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00547_log
def leaf00547 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (48163053371/200000000000) (516144129/1073741824) (-393268061/1073741824) 2 8 ![60,0,4] ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)] affine00547
theorem leaf00547_checked : FastNestedCellData.accepts 1 2 4 leaf00547=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (48163053371/200000000000) (516144129/1073741824) (-393268061/1073741824) 2 8 ![60,0,4] ![(13/800),0,(1/8)] ![(1/3200),1,(1/8)] 11105643991790638655423591219200000000000 6624025528925086991107431344811578228736 27506667726816314397109203763200000000000 raw00547 affine00547
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00547_raw leaf00547_rectangular
    leaf00547_transform leaf00547_sign leaf00547_log
#print axioms leaf00547_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
