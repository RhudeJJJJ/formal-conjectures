/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00497 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 57300725707898917211328217088000000000000 37104296958863414414609259879648385302528 186639616465167476789518270464000000000000))
theorem leaf00497_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 57300725707898917211328217088000000000000 37104296958863414414609259879648385302528 186639616465167476789518270464000000000000 raw00497=true := by decide +kernel
#print axioms leaf00497_raw
theorem leaf00497_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00497=true := by decide +kernel
#print axioms leaf00497_rectangular
def affine00497 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00497 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00497_transform : affine00497=(NestedInteger.clearedAll 3 raw00497 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00497_transform
theorem leaf00497_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00497=true := by decide +kernel
#print axioms leaf00497_sign
theorem leaf00497_log : RationalLog.accepts (2319938913/4294967296) (-661320921/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00497_log
def leaf00497 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24850228519/125000000000) (2319938913/4294967296) (-661320921/2147483648) 1 8 ![60,0,4] ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)] affine00497
theorem leaf00497_checked : FastNestedCellData.accepts 1 2 4 leaf00497=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24850228519/125000000000) (2319938913/4294967296) (-661320921/2147483648) 1 8 ![60,0,4] ![(21/1600),0,(1/8)] ![(1/3200),1,(1/8)] 57300725707898917211328217088000000000000 37104296958863414414609259879648385302528 186639616465167476789518270464000000000000 raw00497 affine00497
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00497_raw leaf00497_rectangular
    leaf00497_transform leaf00497_sign leaf00497_log
#print axioms leaf00497_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
