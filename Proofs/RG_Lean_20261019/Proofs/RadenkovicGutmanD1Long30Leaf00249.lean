/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00249 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 50886831128110134292106969088000000000000 48611849355995254980720617442212547919872 2517435887046250886094884175872000000000000))
theorem leaf00249_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 50886831128110134292106969088000000000000 48611849355995254980720617442212547919872 2517435887046250886094884175872000000000000 raw00249=true := by decide +kernel
#print axioms leaf00249_raw
theorem leaf00249_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00249=true := by decide +kernel
#print axioms leaf00249_rectangular
def affine00249 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00249 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00249_transform : affine00249=(NestedInteger.clearedAll 3 raw00249 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00249_transform
theorem leaf00249_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00249=true := by decide +kernel
#print axioms leaf00249_sign
theorem leaf00249_log : RationalLog.accepts (4025226149/4294967296) (-4352873/134217728) 1 8=true := by decide +kernel
#print axioms leaf00249_log
def leaf00249 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19310064501/1000000000000) (4025226149/4294967296) (-4352873/134217728) 1 8 ![60,0,4] ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00249
theorem leaf00249_checked : FastNestedCellData.accepts 1 2 4 leaf00249=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19310064501/1000000000000) (4025226149/4294967296) (-4352873/134217728) 1 8 ![60,0,4] ![(33/6400),0,(1/2)] ![(1/6400),1,(1/2)] 50886831128110134292106969088000000000000 48611849355995254980720617442212547919872 2517435887046250886094884175872000000000000 raw00249 affine00249
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00249_raw leaf00249_rectangular
    leaf00249_transform leaf00249_sign leaf00249_log
#print axioms leaf00249_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
