/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00208 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 291267953241646999040419692544000000000 177071066879019233396798211384397529088 717719253018637934431303630848000000000))
theorem leaf00208_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 291267953241646999040419692544000000000 177071066879019233396798211384397529088 717719253018637934431303630848000000000 raw00208=true := by decide +kernel
#print axioms leaf00208_raw
theorem leaf00208_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00208=true := by decide +kernel
#print axioms leaf00208_rectangular
def affine00208 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00208 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00208_transform : affine00208=(NestedInteger.clearedAll 3 raw00208 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00208_transform
theorem leaf00208_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00208=true := by decide +kernel
#print axioms leaf00208_sign
theorem leaf00208_log : RationalLog.accepts (2094344307/4294967296) (-1542330165/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00208_log
def leaf00208 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1973708423/8000000000) (2094344307/4294967296) (-1542330165/4294967296) 2 8 ![52,0,4] ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)] affine00208
theorem leaf00208_checked : FastNestedCellData.accepts 1 0 4 leaf00208=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1973708423/8000000000) (2094344307/4294967296) (-1542330165/4294967296) 2 8 ![52,0,4] ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)] 291267953241646999040419692544000000000 177071066879019233396798211384397529088 717719253018637934431303630848000000000 raw00208 affine00208
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00208_raw leaf00208_rectangular
    leaf00208_transform leaf00208_sign leaf00208_log
#print axioms leaf00208_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
