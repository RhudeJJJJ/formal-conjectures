/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00241 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11331427530795005352714698752000000000000 7940059375061305294998713422882455683072 50491570769024744126148509696000000000000))
theorem leaf00241_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11331427530795005352714698752000000000000 7940059375061305294998713422882455683072 50491570769024744126148509696000000000000 raw00241=true := by decide +kernel
#print axioms leaf00241_raw
theorem leaf00241_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00241=true := by decide +kernel
#print axioms leaf00241_rectangular
def affine00241 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00241 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00241_transform : affine00241=(NestedInteger.clearedAll 3 raw00241 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00241_transform
theorem leaf00241_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00241=true := by decide +kernel
#print axioms leaf00241_sign
theorem leaf00241_log : RationalLog.accepts (2600577883/4294967296) (-1077414611/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00241_log
def leaf00241 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9828446677/62500000000) (2600577883/4294967296) (-1077414611/4294967296) 1 8 ![60,0,4] ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)] affine00241
theorem leaf00241_checked : FastNestedCellData.accepts 1 2 4 leaf00241=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9828446677/62500000000) (2600577883/4294967296) (-1077414611/4294967296) 1 8 ![60,0,4] ![(1/200),0,(1/16)] ![(1/6400),1,(1/16)] 11331427530795005352714698752000000000000 7940059375061305294998713422882455683072 50491570769024744126148509696000000000000 raw00241 affine00241
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00241_raw leaf00241_rectangular
    leaf00241_transform leaf00241_sign leaf00241_log
#print axioms leaf00241_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
