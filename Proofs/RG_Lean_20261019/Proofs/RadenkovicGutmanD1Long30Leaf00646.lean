/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00646 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10280978088861954015642806910976000000000000 3134891723729569801720006945282514491539456 5624809704543476444691532087296000000000000))
theorem leaf00646_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10280978088861954015642806910976000000000000 3134891723729569801720006945282514491539456 5624809704543476444691532087296000000000000 raw00646=true := by decide +kernel
#print axioms leaf00646_raw
theorem leaf00646_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00646=true := by decide +kernel
#print axioms leaf00646_rectangular
def affine00646 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00646 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00646_transform : affine00646=(NestedInteger.clearedAll 3 raw00646 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00646_transform
theorem leaf00646_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00646=true := by decide +kernel
#print axioms leaf00646_sign
theorem leaf00646_log : RationalLog.accepts (840942891/4294967296) (-1750924505/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00646_log
def leaf00646 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (557332938961/1000000000000) (840942891/4294967296) (-1750924505/2147483648) 3 8 ![60,0,4] ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)] affine00646
theorem leaf00646_checked : FastNestedCellData.accepts 1 2 4 leaf00646=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (557332938961/1000000000000) (840942891/4294967296) (-1750924505/2147483648) 3 8 ![60,0,4] ![(19/800),0,(1/16)] ![(3/6400),1,(1/16)] 10280978088861954015642806910976000000000000 3134891723729569801720006945282514491539456 5624809704543476444691532087296000000000000 raw00646 affine00646
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00646_raw leaf00646_rectangular
    leaf00646_transform leaf00646_sign leaf00646_log
#print axioms leaf00646_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
