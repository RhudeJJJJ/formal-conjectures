/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00427 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 95187095367473810169420316672000000000000 113191292145115271355506814020017069228032 5483964999437627546363624423424000000000000))
theorem leaf00427_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 95187095367473810169420316672000000000000 113191292145115271355506814020017069228032 5483964999437627546363624423424000000000000 raw00427=true := by decide +kernel
#print axioms leaf00427_raw
theorem leaf00427_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00427=true := by decide +kernel
#print axioms leaf00427_rectangular
def affine00427 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00427 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf00427_transform : affine00427=(NestedInteger.clearedAll 3 raw00427 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/8),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00427_transform
theorem leaf00427_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00427=true := by decide +kernel
#print axioms leaf00427_sign
theorem leaf00427_log : RationalLog.accepts (5004054657/4294967296) (82036331/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00427_log
def leaf00427 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (10320205559/500000000000) (5004054657/4294967296) (82036331/1073741824) 0 8 ![52,0,4] ![(3/8),0,(1/2)] ![(1/32),1,(1/4)] affine00427
theorem leaf00427_checked : FastNestedCellData.accepts 1 0 4 leaf00427=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (10320205559/500000000000) (5004054657/4294967296) (82036331/1073741824) 0 8 ![52,0,4] ![(3/8),0,(1/2)] ![(1/32),1,(1/4)] 95187095367473810169420316672000000000000 113191292145115271355506814020017069228032 5483964999437627546363624423424000000000000 raw00427 affine00427
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00427_raw leaf00427_rectangular
    leaf00427_transform leaf00427_sign leaf00427_log
#print axioms leaf00427_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
