/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00554 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1128694498789487590325436284928000000000000 983684871787214771064827055026309330632704 16076788802018346450957094617088000000000000))
theorem leaf00554_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1128694498789487590325436284928000000000000 983684871787214771064827055026309330632704 16076788802018346450957094617088000000000000 raw00554=true := by decide +kernel
#print axioms leaf00554_raw
theorem leaf00554_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00554=true := by decide +kernel
#print axioms leaf00554_rectangular
def affine00554 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00554 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00554_transform : affine00554=(NestedInteger.clearedAll 3 raw00554 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00554_transform
theorem leaf00554_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00554=true := by decide +kernel
#print axioms leaf00554_sign
theorem leaf00554_log : RationalLog.accepts (3527342791/4294967296) (-211418821/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00554_log
def leaf00554 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (61186651383/1000000000000) (3527342791/4294967296) (-211418821/2147483648) 1 8 ![60,0,4] ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00554
theorem leaf00554_checked : FastNestedCellData.accepts 1 2 4 leaf00554=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (61186651383/1000000000000) (3527342791/4294967296) (-211418821/2147483648) 1 8 ![60,0,4] ![(53/3200),0,(1/2)] ![(1/3200),1,(1/2)] 1128694498789487590325436284928000000000000 983684871787214771064827055026309330632704 16076788802018346450957094617088000000000000 raw00554 affine00554
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00554_raw leaf00554_rectangular
    leaf00554_transform leaf00554_sign leaf00554_log
#print axioms leaf00554_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
