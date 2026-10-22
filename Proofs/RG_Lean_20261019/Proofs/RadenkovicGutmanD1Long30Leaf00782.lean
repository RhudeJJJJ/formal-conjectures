/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00782 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33396279762616504051696664576000000000000 13658169480750672055402996123534740160512 29469594779440834519951736832000000000000))
theorem leaf00782_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33396279762616504051696664576000000000000 13658169480750672055402996123534740160512 29469594779440834519951736832000000000000 raw00782=true := by decide +kernel
#print axioms leaf00782_raw
theorem leaf00782_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00782=true := by decide +kernel
#print axioms leaf00782_rectangular
def affine00782 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00782 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00782_transform : affine00782=(NestedInteger.clearedAll 3 raw00782 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00782_transform
theorem leaf00782_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00782=true := by decide +kernel
#print axioms leaf00782_sign
theorem leaf00782_log : RationalLog.accepts (300062343/1073741824) (-1368929159/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00782_log
def leaf00782 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (115866621029/250000000000) (300062343/1073741824) (-1368929159/2147483648) 2 8 ![60,0,4] ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)] affine00782
theorem leaf00782_checked : FastNestedCellData.accepts 1 2 4 leaf00782=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (115866621029/250000000000) (300062343/1073741824) (-1368929159/2147483648) 2 8 ![60,0,4] ![(31/800),0,(1/8)] ![(3/3200),1,(1/8)] 33396279762616504051696664576000000000000 13658169480750672055402996123534740160512 29469594779440834519951736832000000000000 raw00782 affine00782
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00782_raw leaf00782_rectangular
    leaf00782_transform leaf00782_sign leaf00782_log
#print axioms leaf00782_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
