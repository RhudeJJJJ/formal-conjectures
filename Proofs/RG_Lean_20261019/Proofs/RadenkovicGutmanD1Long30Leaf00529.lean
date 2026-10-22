/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00529 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 62549822163836308237058048000000000000 55154084033448279863236672791905304576 992776253025897945118015488000000000000))
theorem leaf00529_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 62549822163836308237058048000000000000 55154084033448279863236672791905304576 992776253025897945118015488000000000000 raw00529=true := by decide +kernel
#print axioms leaf00529_raw
theorem leaf00529_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00529=true := by decide +kernel
#print axioms leaf00529_rectangular
def affine00529 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00529 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00529_transform : affine00529=(NestedInteger.clearedAll 3 raw00529 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00529_transform
theorem leaf00529_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00529=true := by decide +kernel
#print axioms leaf00529_sign
theorem leaf00529_log : RationalLog.accepts (56059659/67108864) (-386331643/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00529_log
def leaf00529 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27777701101/500000000000) (56059659/67108864) (-386331643/4294967296) 1 8 ![60,0,4] ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)] affine00529
theorem leaf00529_checked : FastNestedCellData.accepts 1 2 4 leaf00529=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27777701101/500000000000) (56059659/67108864) (-386331643/4294967296) 1 8 ![60,0,4] ![(3/200),0,(1/2)] ![(1/3200),1,(1/2)] 62549822163836308237058048000000000000 55154084033448279863236672791905304576 992776253025897945118015488000000000000 raw00529 affine00529
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00529_raw leaf00529_rectangular
    leaf00529_transform leaf00529_sign leaf00529_log
#print axioms leaf00529_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
