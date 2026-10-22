/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00321 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4236826740025200605848282333184000000000000 2546275267360691324701609629099215208579072 11086242388552253319918888419328000000000000))
theorem leaf00321_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4236826740025200605848282333184000000000000 2546275267360691324701609629099215208579072 11086242388552253319918888419328000000000000 raw00321=true := by decide +kernel
#print axioms leaf00321_raw
theorem leaf00321_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00321=true := by decide +kernel
#print axioms leaf00321_rectangular
def affine00321 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00321 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00321_transform : affine00321=(NestedInteger.clearedAll 3 raw00321 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00321_transform
theorem leaf00321_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00321=true := by decide +kernel
#print axioms leaf00321_sign
theorem leaf00321_log : RationalLog.accepts (2099098457/4294967296) (-768730457/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00321_log
def leaf00321 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (229678837799/1000000000000) (2099098457/4294967296) (-768730457/2147483648) 2 8 ![60,0,4] ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)] affine00321
theorem leaf00321_checked : FastNestedCellData.accepts 1 2 4 leaf00321=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (229678837799/1000000000000) (2099098457/4294967296) (-768730457/2147483648) 2 8 ![60,0,4] ![(3/400),0,(1/16)] ![(1/6400),1,(1/16)] 4236826740025200605848282333184000000000000 2546275267360691324701609629099215208579072 11086242388552253319918888419328000000000000 raw00321 affine00321
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00321_raw leaf00321_rectangular
    leaf00321_transform leaf00321_sign leaf00321_log
#print axioms leaf00321_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
