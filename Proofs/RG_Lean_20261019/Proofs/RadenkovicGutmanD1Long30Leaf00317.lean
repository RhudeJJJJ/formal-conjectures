/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00317 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2104766514522465395548876701696000000000000 1628635642379747324761125652835458464350208 14273804090387188633375099322368000000000000))
theorem leaf00317_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2104766514522465395548876701696000000000000 1628635642379747324761125652835458464350208 14273804090387188633375099322368000000000000 raw00317=true := by decide +kernel
#print axioms leaf00317_raw
theorem leaf00317_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00317=true := by decide +kernel
#print axioms leaf00317_rectangular
def affine00317 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00317 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00317_transform : affine00317=(NestedInteger.clearedAll 3 raw00317 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00317_transform
theorem leaf00317_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00317=true := by decide +kernel
#print axioms leaf00317_sign
theorem leaf00317_log : RationalLog.accepts (2983017793/4294967296) (-48923501/268435456) 1 8=true := by decide +kernel
#print axioms leaf00317_log
def leaf00317 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (114099621381/1000000000000) (2983017793/4294967296) (-48923501/268435456) 1 8 ![60,0,4] ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00317
theorem leaf00317_checked : FastNestedCellData.accepts 1 2 4 leaf00317=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (114099621381/1000000000000) (2983017793/4294967296) (-48923501/268435456) 1 8 ![60,0,4] ![(47/6400),0,(1/8)] ![(1/6400),1,(1/8)] 2104766514522465395548876701696000000000000 1628635642379747324761125652835458464350208 14273804090387188633375099322368000000000000 raw00317 affine00317
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00317_raw leaf00317_rectangular
    leaf00317_transform leaf00317_sign leaf00317_log
#print axioms leaf00317_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
