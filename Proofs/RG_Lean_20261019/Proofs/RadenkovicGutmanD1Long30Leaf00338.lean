/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00338 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 281246625761651320638641537024000000000000 244728172754600975843673451600237257818112 4012881895209440935398239895552000000000000))
theorem leaf00338_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 281246625761651320638641537024000000000000 244728172754600975843673451600237257818112 4012881895209440935398239895552000000000000 raw00338=true := by decide +kernel
#print axioms leaf00338_raw
theorem leaf00338_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00338=true := by decide +kernel
#print axioms leaf00338_rectangular
def affine00338 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00338 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00338_transform : affine00338=(NestedInteger.clearedAll 3 raw00338 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00338_transform
theorem leaf00338_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00338=true := by decide +kernel
#print axioms leaf00338_sign
theorem leaf00338_log : RationalLog.accepts (1761233779/2147483648) (-106451947/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00338_log
def leaf00338 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (60985640531/1000000000000) (1761233779/2147483648) (-106451947/1073741824) 1 8 ![60,0,4] ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00338
theorem leaf00338_checked : FastNestedCellData.accepts 1 2 4 leaf00338=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (60985640531/1000000000000) (1761233779/2147483648) (-106451947/1073741824) 1 8 ![60,0,4] ![(51/6400),0,(1/4)] ![(1/6400),1,(1/4)] 281246625761651320638641537024000000000000 244728172754600975843673451600237257818112 4012881895209440935398239895552000000000000 raw00338 affine00338
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00338_raw leaf00338_rectangular
    leaf00338_transform leaf00338_sign leaf00338_log
#print axioms leaf00338_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
