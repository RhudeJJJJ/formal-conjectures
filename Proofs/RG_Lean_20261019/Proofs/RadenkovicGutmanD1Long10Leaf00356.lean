/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00356 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3302992076459686986669621248000000000 2470492095026433010042289609357918208 6633341009473982933709619200000000000))
theorem leaf00356_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3302992076459686986669621248000000000 2470492095026433010042289609357918208 6633341009473982933709619200000000000 raw00356=true := by decide +kernel
#print axioms leaf00356_raw
theorem leaf00356_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00356=true := by decide +kernel
#print axioms leaf00356_rectangular
def affine00356 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00356 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf00356_transform : affine00356=(NestedInteger.clearedAll 3 raw00356 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf00356_transform
theorem leaf00356_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00356=true := by decide +kernel
#print axioms leaf00356_sign
theorem leaf00356_log : RationalLog.accepts (1170344825/2147483648) (-651759515/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00356_log
def leaf00356 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9310889081/25000000000) (1170344825/2147483648) (-651759515/2147483648) 1 8 ![52,0,4] ![(3/16),0,(1/2)] ![(1/80),1,(1/2)] affine00356
theorem leaf00356_checked : FastNestedCellData.accepts 1 0 4 leaf00356=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9310889081/25000000000) (1170344825/2147483648) (-651759515/2147483648) 1 8 ![52,0,4] ![(3/16),0,(1/2)] ![(1/80),1,(1/2)] 3302992076459686986669621248000000000 2470492095026433010042289609357918208 6633341009473982933709619200000000000 raw00356 affine00356
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00356_raw leaf00356_rectangular
    leaf00356_transform leaf00356_sign leaf00356_log
#print axioms leaf00356_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
