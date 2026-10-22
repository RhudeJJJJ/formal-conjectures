/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00265 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1591682055690235399595098112000000000000 843483405958056480606585918742018916352 2386601984476468070282428416000000000000))
theorem leaf00265_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1591682055690235399595098112000000000000 843483405958056480606585918742018916352 2386601984476468070282428416000000000000 raw00265=true := by decide +kernel
#print axioms leaf00265_raw
theorem leaf00265_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00265=true := by decide +kernel
#print axioms leaf00265_rectangular
def affine00265 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00265 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00265_transform : affine00265=(NestedInteger.clearedAll 3 raw00265 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00265_transform
theorem leaf00265_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00265=true := by decide +kernel
#print axioms leaf00265_sign
theorem leaf00265_log : RationalLog.accepts (52552829/134217728) (-2013576059/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00265_log
def leaf00265 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (176712206611/500000000000) (52552829/134217728) (-2013576059/4294967296) 2 8 ![52,0,4] ![(9/160),0,(1/4)] ![(1/640),1,(1/4)] affine00265
theorem leaf00265_checked : FastNestedCellData.accepts 1 0 4 leaf00265=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (176712206611/500000000000) (52552829/134217728) (-2013576059/4294967296) 2 8 ![52,0,4] ![(9/160),0,(1/4)] ![(1/640),1,(1/4)] 1591682055690235399595098112000000000000 843483405958056480606585918742018916352 2386601984476468070282428416000000000000 raw00265 affine00265
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00265_raw leaf00265_rectangular
    leaf00265_transform leaf00265_sign leaf00265_log
#print axioms leaf00265_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
