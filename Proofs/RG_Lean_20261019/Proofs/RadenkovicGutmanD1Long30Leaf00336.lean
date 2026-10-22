/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00336 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7163366003404532972037666242560000000000 4188765610952390635710794085272081399808 17258721595020151598979565486080000000000))
theorem leaf00336_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7163366003404532972037666242560000000000 4188765610952390635710794085272081399808 17258721595020151598979565486080000000000 raw00336=true := by decide +kernel
#print axioms leaf00336_raw
theorem leaf00336_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00336=true := by decide +kernel
#print axioms leaf00336_rectangular
def affine00336 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00336 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00336_transform : affine00336=(NestedInteger.clearedAll 3 raw00336 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00336_transform
theorem leaf00336_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00336=true := by decide +kernel
#print axioms leaf00336_sign
theorem leaf00336_log : RationalLog.accepts (2020975203/4294967296) (-1618910195/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00336_log
def leaf00336 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9708171229/40000000000) (2020975203/4294967296) (-1618910195/4294967296) 2 8 ![60,0,4] ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00336
theorem leaf00336_checked : FastNestedCellData.accepts 1 2 4 leaf00336=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9708171229/40000000000) (2020975203/4294967296) (-1618910195/4294967296) 2 8 ![60,0,4] ![(51/6400),0,(1/16)] ![(1/6400),1,(1/16)] 7163366003404532972037666242560000000000 4188765610952390635710794085272081399808 17258721595020151598979565486080000000000 raw00336 affine00336
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00336_raw leaf00336_rectangular
    leaf00336_transform leaf00336_sign leaf00336_log
#print axioms leaf00336_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
