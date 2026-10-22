/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00445 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 818550495079011984473449299968000000000000 3573250131394656774768721106019274457088 5032892830180846073404194816000000000000))
theorem leaf00445_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 818550495079011984473449299968000000000000 3573250131394656774768721106019274457088 5032892830180846073404194816000000000000 raw00445=true := by decide +kernel
#print axioms leaf00445_raw
theorem leaf00445_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00445=true := by decide +kernel
#print axioms leaf00445_rectangular
def affine00445 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00445 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00445_transform : affine00445=(NestedInteger.clearedAll 3 raw00445 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00445_transform
theorem leaf00445_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00445=true := by decide +kernel
#print axioms leaf00445_sign
theorem leaf00445_log : RationalLog.accepts (2741113/1073741824) (-12821639091/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00445_log
def leaf00445 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (709979380043/1000000000000) (2741113/1073741824) (-12821639091/4294967296) 9 8 ![60,0,4] ![(73/6400),0,0] ![(1/6400),1,(1/16)] affine00445
theorem leaf00445_checked : FastNestedCellData.accepts 1 2 4 leaf00445=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (709979380043/1000000000000) (2741113/1073741824) (-12821639091/4294967296) 9 8 ![60,0,4] ![(73/6400),0,0] ![(1/6400),1,(1/16)] 818550495079011984473449299968000000000000 3573250131394656774768721106019274457088 5032892830180846073404194816000000000000 raw00445 affine00445
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00445_raw leaf00445_rectangular
    leaf00445_transform leaf00445_sign leaf00445_log
#print axioms leaf00445_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
