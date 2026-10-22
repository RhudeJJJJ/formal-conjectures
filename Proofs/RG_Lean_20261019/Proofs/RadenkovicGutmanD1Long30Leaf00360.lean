/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00360 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 180257147886307089449052274688000000000000 429576319963801161809892804234332602368 686890621209257576270659584000000000000))
theorem leaf00360_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 180257147886307089449052274688000000000000 429576319963801161809892804234332602368 686890621209257576270659584000000000000 raw00360=true := by decide +kernel
#print axioms leaf00360_raw
theorem leaf00360_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00360=true := by decide +kernel
#print axioms leaf00360_rectangular
def affine00360 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00360 (IntegerComputedClassCell.leftNumerator ![(7/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/800),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00360_transform : affine00360=(NestedInteger.clearedAll 3 raw00360 (IntegerComputedClassCell.leftNumerator ![(7/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/800),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00360_transform
theorem leaf00360_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00360=true := by decide +kernel
#print axioms leaf00360_sign
theorem leaf00360_log : RationalLog.accepts (1574307/1073741824) (-7006261875/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00360_log
def leaf00360 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (312696306151/500000000000) (1574307/1073741824) (-7006261875/2147483648) 10 8 ![60,0,4] ![(7/800),0,0] ![(1/6400),1,(1/16)] affine00360
theorem leaf00360_checked : FastNestedCellData.accepts 1 2 4 leaf00360=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (312696306151/500000000000) (1574307/1073741824) (-7006261875/2147483648) 10 8 ![60,0,4] ![(7/800),0,0] ![(1/6400),1,(1/16)] 180257147886307089449052274688000000000000 429576319963801161809892804234332602368 686890621209257576270659584000000000000 raw00360 affine00360
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00360_raw leaf00360_rectangular
    leaf00360_transform leaf00360_sign leaf00360_log
#print axioms leaf00360_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
