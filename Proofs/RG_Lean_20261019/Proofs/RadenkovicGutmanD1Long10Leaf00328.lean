/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00328 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 557462498189497710521213779968000000000000 301590749021853487728674464735930783629312 623737850110204886664802729984000000000000))
theorem leaf00328_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 557462498189497710521213779968000000000000 301590749021853487728674464735930783629312 623737850110204886664802729984000000000000 raw00328=true := by decide +kernel
#print axioms leaf00328_raw
theorem leaf00328_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00328=true := by decide +kernel
#print axioms leaf00328_rectangular
def affine00328 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00328 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00328_transform : affine00328=(NestedInteger.clearedAll 3 raw00328 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00328_transform
theorem leaf00328_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00328=true := by decide +kernel
#print axioms leaf00328_sign
theorem leaf00328_log : RationalLog.accepts (391569037/1073741824) (-1083129605/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00328_log
def leaf00328 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (483521641293/1000000000000) (391569037/1073741824) (-1083129605/2147483648) 2 8 ![52,0,4] ![(9/80),0,(1/4)] ![(1/160),1,(1/4)] affine00328
theorem leaf00328_checked : FastNestedCellData.accepts 1 0 4 leaf00328=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (483521641293/1000000000000) (391569037/1073741824) (-1083129605/2147483648) 2 8 ![52,0,4] ![(9/80),0,(1/4)] ![(1/160),1,(1/4)] 557462498189497710521213779968000000000000 301590749021853487728674464735930783629312 623737850110204886664802729984000000000000 raw00328 affine00328
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00328_raw leaf00328_rectangular
    leaf00328_transform leaf00328_sign leaf00328_log
#print axioms leaf00328_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
