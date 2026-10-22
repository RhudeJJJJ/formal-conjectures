/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00296 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3190650342979505773500746956800000000000 2009120340869821452873500991054724202496 9679773911625323597801298329600000000000))
theorem leaf00296_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3190650342979505773500746956800000000000 2009120340869821452873500991054724202496 9679773911625323597801298329600000000000 raw00296=true := by decide +kernel
#print axioms leaf00296_raw
theorem leaf00296_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00296=true := by decide +kernel
#print axioms leaf00296_rectangular
def affine00296 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00296 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00296_transform : affine00296=(NestedInteger.clearedAll 3 raw00296 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00296_transform
theorem leaf00296_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00296=true := by decide +kernel
#print axioms leaf00296_sign
theorem leaf00296_log : RationalLog.accepts (1119820431/2147483648) (-1398287665/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00296_log
def leaf00296 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20755860201/100000000000) (1119820431/2147483648) (-1398287665/4294967296) 1 8 ![60,0,4] ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00296
theorem leaf00296_checked : FastNestedCellData.accepts 1 2 4 leaf00296=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20755860201/100000000000) (1119820431/2147483648) (-1398287665/4294967296) 1 8 ![60,0,4] ![(43/6400),0,(1/16)] ![(1/6400),1,(1/16)] 3190650342979505773500746956800000000000 2009120340869821452873500991054724202496 9679773911625323597801298329600000000000 raw00296 affine00296
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00296_raw leaf00296_rectangular
    leaf00296_transform leaf00296_sign leaf00296_log
#print axioms leaf00296_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
