/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00416 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 86908941212579560933031936000000000000 44262382365716774111866623002595557376 143354099954734555931344896000000000000))
theorem leaf00416_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 86908941212579560933031936000000000000 44262382365716774111866623002595557376 143354099954734555931344896000000000000 raw00416=true := by decide +kernel
#print axioms leaf00416_raw
theorem leaf00416_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00416=true := by decide +kernel
#print axioms leaf00416_rectangular
def affine00416 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00416 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00416_transform : affine00416=(NestedInteger.clearedAll 3 raw00416 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00416_transform
theorem leaf00416_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00416=true := by decide +kernel
#print axioms leaf00416_sign
theorem leaf00416_log : RationalLog.accepts (417839339/1073741824) (-1013406005/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00416_log
def leaf00416 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4824415379/15625000000) (417839339/1073741824) (-1013406005/2147483648) 2 8 ![60,0,4] ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00416
theorem leaf00416_checked : FastNestedCellData.accepts 1 2 4 leaf00416=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4824415379/15625000000) (417839339/1073741824) (-1013406005/2147483648) 2 8 ![60,0,4] ![(67/6400),0,(1/16)] ![(1/6400),1,(1/16)] 86908941212579560933031936000000000000 44262382365716774111866623002595557376 143354099954734555931344896000000000000 raw00416 affine00416
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00416_raw leaf00416_rectangular
    leaf00416_transform leaf00416_sign leaf00416_log
#print axioms leaf00416_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
