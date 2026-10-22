/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00122 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 234576284478345588273521360896000000000000 208124886543627878197149818679910929006592 4091660977129329556547077931008000000000000))
theorem leaf00122_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 234576284478345588273521360896000000000000 208124886543627878197149818679910929006592 4091660977129329556547077931008000000000000 raw00122=true := by decide +kernel
#print axioms leaf00122_raw
theorem leaf00122_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00122=true := by decide +kernel
#print axioms leaf00122_rectangular
def affine00122 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00122 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00122_transform : affine00122=(NestedInteger.clearedAll 3 raw00122 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00122_transform
theorem leaf00122_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00122=true := by decide +kernel
#print axioms leaf00122_sign
theorem leaf00122_log : RationalLog.accepts (1813103479/2147483648) (-90869037/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00122_log
def leaf00122 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (50865623449/1000000000000) (1813103479/2147483648) (-90869037/1073741824) 1 8 ![52,0,4] ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)] affine00122
theorem leaf00122_checked : FastNestedCellData.accepts 1 0 4 leaf00122=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (50865623449/1000000000000) (1813103479/2147483648) (-90869037/1073741824) 1 8 ![52,0,4] ![(11/800),0,(1/2)] ![(1/1600),1,(1/2)] 234576284478345588273521360896000000000000 208124886543627878197149818679910929006592 4091660977129329556547077931008000000000000 raw00122 affine00122
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00122_raw leaf00122_rectangular
    leaf00122_transform leaf00122_sign leaf00122_log
#print axioms leaf00122_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
