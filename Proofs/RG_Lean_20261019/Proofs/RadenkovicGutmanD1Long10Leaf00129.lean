/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00129 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 24531815143498388945839849472000000000000 97175064850712093028256678140211888128 285433480264818876286500864000000000000))
theorem leaf00129_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 24531815143498388945839849472000000000000 97175064850712093028256678140211888128 285433480264818876286500864000000000000 raw00129=true := by decide +kernel
#print axioms leaf00129_raw
theorem leaf00129_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00129=true := by decide +kernel
#print axioms leaf00129_rectangular
def affine00129 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00129 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00129_transform : affine00129=(NestedInteger.clearedAll 3 raw00129 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00129_transform
theorem leaf00129_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00129=true := by decide +kernel
#print axioms leaf00129_sign
theorem leaf00129_log : RationalLog.accepts (1586519/536870912) (-3126851897/1073741824) 9 8=true := by decide +kernel
#print axioms leaf00129_log
def leaf00129 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (170223662551/500000000000) (1586519/536870912) (-3126851897/1073741824) 9 8 ![52,0,4] ![(1/64),0,0] ![(1/1600),1,(1/4)] affine00129
theorem leaf00129_checked : FastNestedCellData.accepts 1 0 4 leaf00129=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (170223662551/500000000000) (1586519/536870912) (-3126851897/1073741824) 9 8 ![52,0,4] ![(1/64),0,0] ![(1/1600),1,(1/4)] 24531815143498388945839849472000000000000 97175064850712093028256678140211888128 285433480264818876286500864000000000000 raw00129 affine00129
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00129_raw leaf00129_rectangular
    leaf00129_transform leaf00129_sign leaf00129_log
#print axioms leaf00129_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
