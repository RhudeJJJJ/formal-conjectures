/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00485 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 213062217114966588418921857024000000000000 1171508831272458491388248692890519207936 1584816095856695312191062016000000000000))
theorem leaf00485_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 213062217114966588418921857024000000000000 1171508831272458491388248692890519207936 1584816095856695312191062016000000000000 raw00485=true := by decide +kernel
#print axioms leaf00485_raw
theorem leaf00485_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00485=true := by decide +kernel
#print axioms leaf00485_rectangular
def affine00485 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00485 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(81/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00485_transform : affine00485=(NestedInteger.clearedAll 3 raw00485 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(81/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00485_transform
theorem leaf00485_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00485=true := by decide +kernel
#print axioms leaf00485_sign
theorem leaf00485_log : RationalLog.accepts (3394591/1073741824) (-12362465769/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00485_log
def leaf00485 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (369604029873/500000000000) (3394591/1073741824) (-12362465769/4294967296) 9 8 ![60,0,4] ![(81/6400),0,0] ![(1/6400),1,(1/16)] affine00485
theorem leaf00485_checked : FastNestedCellData.accepts 1 2 4 leaf00485=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (369604029873/500000000000) (3394591/1073741824) (-12362465769/4294967296) 9 8 ![60,0,4] ![(81/6400),0,0] ![(1/6400),1,(1/16)] 213062217114966588418921857024000000000000 1171508831272458491388248692890519207936 1584816095856695312191062016000000000000 raw00485 affine00485
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00485_raw leaf00485_rectangular
    leaf00485_transform leaf00485_sign leaf00485_log
#print axioms leaf00485_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
