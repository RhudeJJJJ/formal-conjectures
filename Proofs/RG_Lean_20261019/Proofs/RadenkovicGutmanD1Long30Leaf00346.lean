/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00346 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2519190925884735854754974924800000000000 1446806816670353588182553910519202316288 5757730888608899777737785344000000000000))
theorem leaf00346_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2519190925884735854754974924800000000000 1446806816670353588182553910519202316288 5757730888608899777737785344000000000000 raw00346=true := by decide +kernel
#print axioms leaf00346_raw
theorem leaf00346_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00346=true := by decide +kernel
#print axioms leaf00346_rectangular
def affine00346 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00346 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00346_transform : affine00346=(NestedInteger.clearedAll 3 raw00346 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00346_transform
theorem leaf00346_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00346=true := by decide +kernel
#print axioms leaf00346_sign
theorem leaf00346_log : RationalLog.accepts (492827095/1073741824) (-836172687/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00346_log
def leaf00346 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (251280729277/1000000000000) (492827095/1073741824) (-836172687/2147483648) 2 8 ![60,0,4] ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00346
theorem leaf00346_checked : FastNestedCellData.accepts 1 2 4 leaf00346=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (251280729277/1000000000000) (492827095/1073741824) (-836172687/2147483648) 2 8 ![60,0,4] ![(53/6400),0,(1/16)] ![(1/6400),1,(1/16)] 2519190925884735854754974924800000000000 1446806816670353588182553910519202316288 5757730888608899777737785344000000000000 raw00346 affine00346
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00346_raw leaf00346_rectangular
    leaf00346_transform leaf00346_sign leaf00346_log
#print axioms leaf00346_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
