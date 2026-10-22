/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00021 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9305970966069887040614091980800000000000 8461299641489065005641941832708508352512 209654948401688080376427184128000000000000))
theorem leaf00021_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9305970966069887040614091980800000000000 8461299641489065005641941832708508352512 209654948401688080376427184128000000000000 raw00021=true := by decide +kernel
#print axioms leaf00021_raw
theorem leaf00021_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00021=true := by decide +kernel
#print axioms leaf00021_rectangular
def affine00021 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00021 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00021_transform : affine00021=(NestedInteger.clearedAll 3 raw00021 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00021_transform
theorem leaf00021_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00021=true := by decide +kernel
#print axioms leaf00021_sign
theorem leaf00021_log : RationalLog.accepts (1876818805/2147483648) (-289305901/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00021_log
def leaf00021 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20179107877/500000000000) (1876818805/2147483648) (-289305901/4294967296) 1 8 ![60,0,4] ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)] affine00021
theorem leaf00021_checked : FastNestedCellData.accepts 1 2 4 leaf00021=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20179107877/500000000000) (1876818805/2147483648) (-289305901/4294967296) 1 8 ![60,0,4] ![(1/800),0,(1/16)] ![(1/16000),1,(1/16)] 9305970966069887040614091980800000000000 8461299641489065005641941832708508352512 209654948401688080376427184128000000000000 raw00021 affine00021
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00021_raw leaf00021_rectangular
    leaf00021_transform leaf00021_sign leaf00021_log
#print axioms leaf00021_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
