/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00497 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 46030102841052213805056000000000000 46033260283107692940156668410331136 288250147359142467643233009664000000000000))
theorem leaf00497_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 46030102841052213805056000000000000 46033260283107692940156668410331136 288250147359142467643233009664000000000000 raw00497=true := by decide +kernel
#print axioms leaf00497_raw
theorem leaf00497_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00497=true := by decide +kernel
#print axioms leaf00497_rectangular
def affine00497 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00497 (IntegerComputedClassCell.leftNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(3/512),0,0] ![(1/512),1,1]))
theorem leaf00497_transform : affine00497=(NestedInteger.clearedAll 3 raw00497 (IntegerComputedClassCell.leftNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(3/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf00497_transform
theorem leaf00497_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00497=true := by decide +kernel
#print axioms leaf00497_sign
theorem leaf00497_log : RationalLog.accepts (536907653/536870912) (73479/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00497_log
def leaf00497 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (159699/1000000000000) (536907653/536870912) (73479/2147483648) 0 8 ![52,0,4] ![(3/512),0,0] ![(1/512),1,1] affine00497
theorem leaf00497_checked : FastNestedCellData.accepts 1 0 4 leaf00497=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (159699/1000000000000) (536907653/536870912) (73479/2147483648) 0 8 ![52,0,4] ![(3/512),0,0] ![(1/512),1,1] 46030102841052213805056000000000000 46033260283107692940156668410331136 288250147359142467643233009664000000000000 raw00497 affine00497
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00497_raw leaf00497_rectangular
    leaf00497_transform leaf00497_sign leaf00497_log
#print axioms leaf00497_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
