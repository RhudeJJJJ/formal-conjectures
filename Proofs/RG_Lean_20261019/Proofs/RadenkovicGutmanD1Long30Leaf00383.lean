/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00383 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 42546573093697371887563177984000000000000 36196579763598501222703342095487314427904 506245270271061847573545353216000000000000))
theorem leaf00383_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 42546573093697371887563177984000000000000 36196579763598501222703342095487314427904 506245270271061847573545353216000000000000 raw00383=true := by decide +kernel
#print axioms leaf00383_raw
theorem leaf00383_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00383=true := by decide +kernel
#print axioms leaf00383_rectangular
def affine00383 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00383 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00383_transform : affine00383=(NestedInteger.clearedAll 3 raw00383 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00383_transform
theorem leaf00383_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00383=true := by decide +kernel
#print axioms leaf00383_sign
theorem leaf00383_log : RationalLog.accepts (3410127379/4294967296) (-61926533/536870912) 1 8=true := by decide +kernel
#print axioms leaf00383_log
def leaf00383 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71500084819/1000000000000) (3410127379/4294967296) (-61926533/536870912) 1 8 ![60,0,4] ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)] affine00383
theorem leaf00383_checked : FastNestedCellData.accepts 1 2 4 leaf00383=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71500084819/1000000000000) (3410127379/4294967296) (-61926533/536870912) 1 8 ![60,0,4] ![(3/320),0,(1/4)] ![(1/6400),1,(1/4)] 42546573093697371887563177984000000000000 36196579763598501222703342095487314427904 506245270271061847573545353216000000000000 raw00383 affine00383
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00383_raw leaf00383_rectangular
    leaf00383_transform leaf00383_sign leaf00383_log
#print axioms leaf00383_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
