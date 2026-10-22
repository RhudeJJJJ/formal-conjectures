/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00464 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 202613211511469271823864037376000000000000 183328914801288639875489593566218529275904 4172755502247740456084455817216000000000000))
theorem leaf00464_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 202613211511469271823864037376000000000000 183328914801288639875489593566218529275904 4172755502247740456084455817216000000000000 raw00464=true := by decide +kernel
#print axioms leaf00464_raw
theorem leaf00464_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00464=true := by decide +kernel
#print axioms leaf00464_rectangular
def affine00464 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00464 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00464_transform : affine00464=(NestedInteger.clearedAll 3 raw00464 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00464_transform
theorem leaf00464_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00464=true := by decide +kernel
#print axioms leaf00464_sign
theorem leaf00464_log : RationalLog.accepts (1861314343/2147483648) (-153560009/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00464_log
def leaf00464 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43934736819/1000000000000) (1861314343/2147483648) (-153560009/2147483648) 1 8 ![60,0,4] ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)] affine00464
theorem leaf00464_checked : FastNestedCellData.accepts 1 2 4 leaf00464=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43934736819/1000000000000) (1861314343/2147483648) (-153560009/2147483648) 1 8 ![60,0,4] ![(19/1600),0,(1/2)] ![(1/6400),1,(1/2)] 202613211511469271823864037376000000000000 183328914801288639875489593566218529275904 4172755502247740456084455817216000000000000 raw00464 affine00464
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00464_raw leaf00464_rectangular
    leaf00464_transform leaf00464_sign leaf00464_log
#print axioms leaf00464_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
