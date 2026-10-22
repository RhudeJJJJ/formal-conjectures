/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00368 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 568598104928850021607232503808000000000000 495519026910062829844190303832679139770368 1339656339839443592645053513728000000000000))
theorem leaf00368_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 568598104928850021607232503808000000000000 495519026910062829844190303832679139770368 1339656339839443592645053513728000000000000 raw00368=true := by decide +kernel
#print axioms leaf00368_raw
theorem leaf00368_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00368=true := by decide +kernel
#print axioms leaf00368_rectangular
def affine00368 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00368 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf00368_transform : affine00368=(NestedInteger.clearedAll 3 raw00368 (IntegerComputedClassCell.leftNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/160),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00368_transform
theorem leaf00368_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00368=true := by decide +kernel
#print axioms leaf00368_sign
theorem leaf00368_log : RationalLog.accepts (1366157043/2147483648) (-971296239/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00368_log
def leaf00368 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (369885180381/1000000000000) (1366157043/2147483648) (-971296239/4294967296) 1 8 ![52,0,4] ![(41/160),0,(1/2)] ![(3/160),1,(1/2)] affine00368
theorem leaf00368_checked : FastNestedCellData.accepts 1 0 4 leaf00368=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (369885180381/1000000000000) (1366157043/2147483648) (-971296239/4294967296) 1 8 ![52,0,4] ![(41/160),0,(1/2)] ![(3/160),1,(1/2)] 568598104928850021607232503808000000000000 495519026910062829844190303832679139770368 1339656339839443592645053513728000000000000 raw00368 affine00368
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00368_raw leaf00368_rectangular
    leaf00368_transform leaf00368_sign leaf00368_log
#print axioms leaf00368_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
