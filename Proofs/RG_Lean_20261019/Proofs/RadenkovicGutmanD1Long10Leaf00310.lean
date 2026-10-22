/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00310 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8360726028466977136490888298496000000000000 4317970998244825267984152869727528751726592 9526984337379074724237601144832000000000000))
theorem leaf00310_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8360726028466977136490888298496000000000000 4317970998244825267984152869727528751726592 9526984337379074724237601144832000000000000 raw00310=true := by decide +kernel
#print axioms leaf00310_raw
theorem leaf00310_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00310=true := by decide +kernel
#print axioms leaf00310_rectangular
def affine00310 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00310 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00310_transform : affine00310=(NestedInteger.clearedAll 3 raw00310 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00310_transform
theorem leaf00310_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00310=true := by decide +kernel
#print axioms leaf00310_sign
theorem leaf00310_log : RationalLog.accepts (1526368807/4294967296) (-2221684337/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00310_log
def leaf00310 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (453235866181/1000000000000) (1526368807/4294967296) (-2221684337/4294967296) 2 8 ![52,0,4] ![(29/320),0,(1/4)] ![(1/320),1,(1/4)] affine00310
theorem leaf00310_checked : FastNestedCellData.accepts 1 0 4 leaf00310=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (453235866181/1000000000000) (1526368807/4294967296) (-2221684337/4294967296) 2 8 ![52,0,4] ![(29/320),0,(1/4)] ![(1/320),1,(1/4)] 8360726028466977136490888298496000000000000 4317970998244825267984152869727528751726592 9526984337379074724237601144832000000000000 raw00310 affine00310
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00310_raw leaf00310_rectangular
    leaf00310_transform leaf00310_sign leaf00310_log
#print axioms leaf00310_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
