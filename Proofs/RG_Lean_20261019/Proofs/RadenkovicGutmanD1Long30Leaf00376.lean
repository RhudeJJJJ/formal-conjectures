/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00376 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1275017216665355922080857587712000000000000 694623526998859807245533616309550926790656 2512425374074089260660715159552000000000000))
theorem leaf00376_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1275017216665355922080857587712000000000000 694623526998859807245533616309550926790656 2512425374074089260660715159552000000000000 raw00376=true := by decide +kernel
#print axioms leaf00376_raw
theorem leaf00376_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00376=true := by decide +kernel
#print axioms leaf00376_rectangular
def affine00376 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00376 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00376_transform : affine00376=(NestedInteger.clearedAll 3 raw00376 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00376_transform
theorem leaf00376_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00376=true := by decide +kernel
#print axioms leaf00376_sign
theorem leaf00376_log : RationalLog.accepts (916538883/2147483648) (-457117439/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00376_log
def leaf00376 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (276475287253/1000000000000) (916538883/2147483648) (-457117439/1073741824) 2 8 ![60,0,4] ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00376
theorem leaf00376_checked : FastNestedCellData.accepts 1 2 4 leaf00376=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (276475287253/1000000000000) (916538883/2147483648) (-457117439/1073741824) 2 8 ![60,0,4] ![(59/6400),0,(1/16)] ![(1/6400),1,(1/16)] 1275017216665355922080857587712000000000000 694623526998859807245533616309550926790656 2512425374074089260660715159552000000000000 raw00376 affine00376
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00376_raw leaf00376_rectangular
    leaf00376_transform leaf00376_sign leaf00376_log
#print axioms leaf00376_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
