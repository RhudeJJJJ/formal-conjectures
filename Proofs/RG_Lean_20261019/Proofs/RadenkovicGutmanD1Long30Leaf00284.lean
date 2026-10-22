/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00284 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 107616507539842586127017967616000000000000 101878510003275641585552803324610962522112 4365795832822176066908903702528000000000000))
theorem leaf00284_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 107616507539842586127017967616000000000000 101878510003275641585552803324610962522112 4365795832822176066908903702528000000000000 raw00284=true := by decide +kernel
#print axioms leaf00284_raw
theorem leaf00284_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00284=true := by decide +kernel
#print axioms leaf00284_rectangular
def affine00284 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00284 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00284_transform : affine00284=(NestedInteger.clearedAll 3 raw00284 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00284_transform
theorem leaf00284_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00284=true := by decide +kernel
#print axioms leaf00284_sign
theorem leaf00284_log : RationalLog.accepts (3973246093/4294967296) (-10450265/268435456) 1 8=true := by decide +kernel
#print axioms leaf00284_log
def leaf00284 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11667805127/500000000000) (3973246093/4294967296) (-10450265/268435456) 1 8 ![60,0,4] ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)] affine00284
theorem leaf00284_checked : FastNestedCellData.accepts 1 2 4 leaf00284=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11667805127/500000000000) (3973246093/4294967296) (-10450265/268435456) 1 8 ![60,0,4] ![(1/160),0,(1/2)] ![(1/6400),1,(1/2)] 107616507539842586127017967616000000000000 101878510003275641585552803324610962522112 4365795832822176066908903702528000000000000 raw00284 affine00284
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00284_raw leaf00284_rectangular
    leaf00284_transform leaf00284_sign leaf00284_log
#print axioms leaf00284_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
