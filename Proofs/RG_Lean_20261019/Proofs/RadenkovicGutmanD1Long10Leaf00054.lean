/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00054 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 10853428132802719119938315878400000000000 3029680077622617389731060349065494528 21455484054315113725820928000000000000))
theorem leaf00054_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 10853428132802719119938315878400000000000 3029680077622617389731060349065494528 21455484054315113725820928000000000000 raw00054=true := by decide +kernel
#print axioms leaf00054_raw
theorem leaf00054_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00054=true := by decide +kernel
#print axioms leaf00054_rectangular
def affine00054 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00054 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00054_transform : affine00054=(NestedInteger.clearedAll 3 raw00054 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00054_transform
theorem leaf00054_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00054=true := by decide +kernel
#print axioms leaf00054_sign
theorem leaf00054_log : RationalLog.accepts (525285/2147483648) (-4464546855/1073741824) 12 8=true := by decide +kernel
#print axioms leaf00054_log
def leaf00054 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (70603862163/500000000000) (525285/2147483648) (-4464546855/1073741824) 12 8 ![52,0,4] ![(19/3200),0,0] ![(1/3200),1,(1/4)] affine00054
theorem leaf00054_checked : FastNestedCellData.accepts 1 0 4 leaf00054=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (70603862163/500000000000) (525285/2147483648) (-4464546855/1073741824) 12 8 ![52,0,4] ![(19/3200),0,0] ![(1/3200),1,(1/4)] 10853428132802719119938315878400000000000 3029680077622617389731060349065494528 21455484054315113725820928000000000000 raw00054 affine00054
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00054_raw leaf00054_rectangular
    leaf00054_transform leaf00054_sign leaf00054_log
#print axioms leaf00054_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
