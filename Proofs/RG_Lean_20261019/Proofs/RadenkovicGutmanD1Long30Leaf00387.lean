/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00387 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 675627396808037295753346940928000000000000 488473259199497865129227182228526981971968 3334212482307058048866004762624000000000000))
theorem leaf00387_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 675627396808037295753346940928000000000000 488473259199497865129227182228526981971968 3334212482307058048866004762624000000000000 raw00387=true := by decide +kernel
#print axioms leaf00387_raw
theorem leaf00387_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00387=true := by decide +kernel
#print axioms leaf00387_rectangular
def affine00387 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00387 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00387_transform : affine00387=(NestedInteger.clearedAll 3 raw00387 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00387_transform
theorem leaf00387_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00387=true := by decide +kernel
#print axioms leaf00387_sign
theorem leaf00387_log : RationalLog.accepts (2708432893/4294967296) (-247537089/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00387_log
def leaf00387 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (73251669141/500000000000) (2708432893/4294967296) (-247537089/1073741824) 1 8 ![60,0,4] ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00387
theorem leaf00387_checked : FastNestedCellData.accepts 1 2 4 leaf00387=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (73251669141/500000000000) (2708432893/4294967296) (-247537089/1073741824) 1 8 ![60,0,4] ![(61/6400),0,(1/8)] ![(1/6400),1,(1/8)] 675627396808037295753346940928000000000000 488473259199497865129227182228526981971968 3334212482307058048866004762624000000000000 raw00387 affine00387
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00387_raw leaf00387_rectangular
    leaf00387_transform leaf00387_sign leaf00387_log
#print axioms leaf00387_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
