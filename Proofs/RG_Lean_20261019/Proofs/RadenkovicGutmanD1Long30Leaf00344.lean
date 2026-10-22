/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00344 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 139382085325069224776902377472000000000000 129942470554020944668929985412092798173184 4299360805632237889226945855488000000000000))
theorem leaf00344_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 139382085325069224776902377472000000000000 129942470554020944668929985412092798173184 4299360805632237889226945855488000000000000 raw00344=true := by decide +kernel
#print axioms leaf00344_raw
theorem leaf00344_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00344=true := by decide +kernel
#print axioms leaf00344_rectangular
def affine00344 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00344 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00344_transform : affine00344=(NestedInteger.clearedAll 3 raw00344 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00344_transform
theorem leaf00344_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00344=true := by decide +kernel
#print axioms leaf00344_sign
theorem leaf00344_log : RationalLog.accepts (1943311867/2147483648) (-214540299/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00344_log
def leaf00344 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (30223671943/1000000000000) (1943311867/2147483648) (-214540299/4294967296) 1 8 ![60,0,4] ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)] affine00344
theorem leaf00344_checked : FastNestedCellData.accepts 1 2 4 leaf00344=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (30223671943/1000000000000) (1943311867/2147483648) (-214540299/4294967296) 1 8 ![60,0,4] ![(13/1600),0,(1/2)] ![(1/6400),1,(1/2)] 139382085325069224776902377472000000000000 129942470554020944668929985412092798173184 4299360805632237889226945855488000000000000 raw00344 affine00344
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00344_raw leaf00344_rectangular
    leaf00344_transform leaf00344_sign leaf00344_log
#print axioms leaf00344_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
