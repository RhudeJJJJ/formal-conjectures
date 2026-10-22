/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00213 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 170774221614592797727713656832000000000000 5445642661790151091792732901370041991168 9191080585557536207332704256000000000000))
theorem leaf00213_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 170774221614592797727713656832000000000000 5445642661790151091792732901370041991168 9191080585557536207332704256000000000000 raw00213=true := by decide +kernel
#print axioms leaf00213_raw
theorem leaf00213_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00213=true := by decide +kernel
#print axioms leaf00213_rectangular
def affine00213 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00213 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/1600),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00213_transform : affine00213=(NestedInteger.clearedAll 3 raw00213 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/1600),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00213_transform
theorem leaf00213_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00213=true := by decide +kernel
#print axioms leaf00213_sign
theorem leaf00213_log : RationalLog.accepts (10750271/536870912) (-1049804579/536870912) 6 8=true := by decide +kernel
#print axioms leaf00213_log
def leaf00213 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (592492102653/1000000000000) (10750271/536870912) (-1049804579/536870912) 6 8 ![52,0,4] ![(59/1600),0,0] ![(3/3200),1,(1/4)] affine00213
theorem leaf00213_checked : FastNestedCellData.accepts 1 0 4 leaf00213=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (592492102653/1000000000000) (10750271/536870912) (-1049804579/536870912) 6 8 ![52,0,4] ![(59/1600),0,0] ![(3/3200),1,(1/4)] 170774221614592797727713656832000000000000 5445642661790151091792732901370041991168 9191080585557536207332704256000000000000 raw00213 affine00213
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00213_raw leaf00213_rectangular
    leaf00213_transform leaf00213_sign leaf00213_log
#print axioms leaf00213_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
