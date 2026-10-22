/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00371 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 50236595669363693225551226470400000000000 27606790648405017225014375289801142173696 101371399674315521179693508198400000000000))
theorem leaf00371_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 50236595669363693225551226470400000000000 27606790648405017225014375289801142173696 101371399674315521179693508198400000000000 raw00371=true := by decide +kernel
#print axioms leaf00371_raw
theorem leaf00371_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00371=true := by decide +kernel
#print axioms leaf00371_rectangular
def affine00371 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00371 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00371_transform : affine00371=(NestedInteger.clearedAll 3 raw00371 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00371_transform
theorem leaf00371_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00371=true := by decide +kernel
#print axioms leaf00371_sign
theorem leaf00371_log : RationalLog.accepts (927523133/2147483648) (-1802886261/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00371_log
def leaf00371 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (54466626163/200000000000) (927523133/2147483648) (-1802886261/4294967296) 2 8 ![60,0,4] ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00371
theorem leaf00371_checked : FastNestedCellData.accepts 1 2 4 leaf00371=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (54466626163/200000000000) (927523133/2147483648) (-1802886261/4294967296) 2 8 ![60,0,4] ![(29/3200),0,(1/16)] ![(1/6400),1,(1/16)] 50236595669363693225551226470400000000000 27606790648405017225014375289801142173696 101371399674315521179693508198400000000000 raw00371 affine00371
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00371_raw leaf00371_rectangular
    leaf00371_transform leaf00371_sign leaf00371_log
#print axioms leaf00371_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
