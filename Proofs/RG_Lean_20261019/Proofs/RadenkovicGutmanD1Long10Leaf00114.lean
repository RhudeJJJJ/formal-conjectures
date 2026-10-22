/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00114 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 325876830488894606141175103488000000000000 717401044499604058765568873080641552384 2538097263282403450990624768000000000000))
theorem leaf00114_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 325876830488894606141175103488000000000000 717401044499604058765568873080641552384 2538097263282403450990624768000000000000 raw00114=true := by decide +kernel
#print axioms leaf00114_raw
theorem leaf00114_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00114=true := by decide +kernel
#print axioms leaf00114_rectangular
def affine00114 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00114 (IntegerComputedClassCell.leftNumerator ![(1/80),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/80),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00114_transform : affine00114=(NestedInteger.clearedAll 3 raw00114 (IntegerComputedClassCell.leftNumerator ![(1/80),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/80),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00114_transform
theorem leaf00114_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00114=true := by decide +kernel
#print axioms leaf00114_sign
theorem leaf00114_log : RationalLog.accepts (1842889/1073741824) (-6837126843/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00114_log
def leaf00114 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (282653094063/1000000000000) (1842889/1073741824) (-6837126843/2147483648) 10 8 ![52,0,4] ![(1/80),0,0] ![(1/1600),1,(1/4)] affine00114
theorem leaf00114_checked : FastNestedCellData.accepts 1 0 4 leaf00114=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (282653094063/1000000000000) (1842889/1073741824) (-6837126843/2147483648) 10 8 ![52,0,4] ![(1/80),0,0] ![(1/1600),1,(1/4)] 325876830488894606141175103488000000000000 717401044499604058765568873080641552384 2538097263282403450990624768000000000000 raw00114 affine00114
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00114_raw leaf00114_rectangular
    leaf00114_transform leaf00114_sign leaf00114_log
#print axioms leaf00114_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
