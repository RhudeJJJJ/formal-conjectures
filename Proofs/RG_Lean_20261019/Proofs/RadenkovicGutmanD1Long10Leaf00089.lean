/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00089 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 53148903767549334478015954944000000000000 48970011014857831270091990360711554400256 1416362327416059466795221778432000000000000))
theorem leaf00089_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 53148903767549334478015954944000000000000 48970011014857831270091990360711554400256 1416362327416059466795221778432000000000000 raw00089=true := by decide +kernel
#print axioms leaf00089_raw
theorem leaf00089_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00089=true := by decide +kernel
#print axioms leaf00089_rectangular
def affine00089 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00089 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00089_transform : affine00089=(NestedInteger.clearedAll 3 raw00089 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00089_transform
theorem leaf00089_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00089=true := by decide +kernel
#print axioms leaf00089_sign
theorem leaf00089_log : RationalLog.accepts (3825022413/4294967296) (-62212403/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00089_log
def leaf00089 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17287247079/500000000000) (3825022413/4294967296) (-62212403/1073741824) 1 8 ![52,0,4] ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)] affine00089
theorem leaf00089_checked : FastNestedCellData.accepts 1 0 4 leaf00089=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17287247079/500000000000) (3825022413/4294967296) (-62212403/1073741824) 1 8 ![52,0,4] ![(3/320),0,(1/2)] ![(1/3200),1,(1/2)] 53148903767549334478015954944000000000000 48970011014857831270091990360711554400256 1416362327416059466795221778432000000000000 raw00089 affine00089
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00089_raw leaf00089_rectangular
    leaf00089_transform leaf00089_sign leaf00089_log
#print axioms leaf00089_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
