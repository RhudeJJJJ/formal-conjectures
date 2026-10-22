/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00341 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 63343420975222403678535365427200000000000 42900567540083286638229936406805964914688 124934172775159171577331213926400000000000))
theorem leaf00341_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 63343420975222403678535365427200000000000 42900567540083286638229936406805964914688 124934172775159171577331213926400000000000 raw00341=true := by decide +kernel
#print axioms leaf00341_raw
theorem leaf00341_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00341=true := by decide +kernel
#print axioms leaf00341_rectangular
def affine00341 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00341 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00341_transform : affine00341=(NestedInteger.clearedAll 3 raw00341 (IntegerComputedClassCell.leftNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/80),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00341_transform
theorem leaf00341_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00341=true := by decide +kernel
#print axioms leaf00341_sign
theorem leaf00341_log : RationalLog.accepts (2165313427/4294967296) (-1470766103/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00341_log
def leaf00341 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (34338537317/100000000000) (2165313427/4294967296) (-1470766103/4294967296) 1 8 ![52,0,4] ![(11/80),0,(1/2)] ![(1/160),1,(1/2)] affine00341
theorem leaf00341_checked : FastNestedCellData.accepts 1 0 4 leaf00341=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (34338537317/100000000000) (2165313427/4294967296) (-1470766103/4294967296) 1 8 ![52,0,4] ![(11/80),0,(1/2)] ![(1/160),1,(1/2)] 63343420975222403678535365427200000000000 42900567540083286638229936406805964914688 124934172775159171577331213926400000000000 raw00341 affine00341
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00341_raw leaf00341_rectangular
    leaf00341_transform leaf00341_sign leaf00341_log
#print axioms leaf00341_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
