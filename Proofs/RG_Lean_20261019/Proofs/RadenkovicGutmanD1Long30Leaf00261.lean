/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00261 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10133563327262556039519456460800000000000 6825606384930990330632815054499459629056 38828337718073682152145289216000000000000))
theorem leaf00261_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10133563327262556039519456460800000000000 6825606384930990330632815054499459629056 38828337718073682152145289216000000000000 raw00261=true := by decide +kernel
#print axioms leaf00261_raw
theorem leaf00261_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00261=true := by decide +kernel
#print axioms leaf00261_rectangular
def affine00261 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00261 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00261_transform : affine00261=(NestedInteger.clearedAll 3 raw00261 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00261_transform
theorem leaf00261_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00261=true := by decide +kernel
#print axioms leaf00261_sign
theorem leaf00261_log : RationalLog.accepts (307552615/536870912) (-37387121/134217728) 1 8=true := by decide +kernel
#print axioms leaf00261_log
def leaf00261 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (175789301991/1000000000000) (307552615/536870912) (-37387121/134217728) 1 8 ![60,0,4] ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)] affine00261
theorem leaf00261_checked : FastNestedCellData.accepts 1 2 4 leaf00261=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (175789301991/1000000000000) (307552615/536870912) (-37387121/134217728) 1 8 ![60,0,4] ![(9/1600),0,(1/16)] ![(1/6400),1,(1/16)] 10133563327262556039519456460800000000000 6825606384930990330632815054499459629056 38828337718073682152145289216000000000000 raw00261 affine00261
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00261_raw leaf00261_rectangular
    leaf00261_transform leaf00261_sign leaf00261_log
#print axioms leaf00261_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
