/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00463 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 9435874968362303616672858112000000000000 9780579001096918897997834529902935670784 6373542052039520793504570671104000000000000))
theorem leaf00463_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 9435874968362303616672858112000000000000 9780579001096918897997834529902935670784 6373542052039520793504570671104000000000000 raw00463=true := by decide +kernel
#print axioms leaf00463_raw
theorem leaf00463_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00463=true := by decide +kernel
#print axioms leaf00463_rectangular
def affine00463 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00463 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00463_transform : affine00463=(NestedInteger.clearedAll 3 raw00463 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00463_transform
theorem leaf00463_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00463=true := by decide +kernel
#print axioms leaf00463_sign
theorem leaf00463_log : RationalLog.accepts (4445046507/4294967296) (9219789/536870912) 0 8=true := by decide +kernel
#print axioms leaf00463_log
def leaf00463 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1534559421/1000000000000) (4445046507/4294967296) (9219789/536870912) 0 8 ![52,0,4] ![(9/64),0,(1/2)] ![(1/64),1,(1/4)] affine00463
theorem leaf00463_checked : FastNestedCellData.accepts 1 0 4 leaf00463=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1534559421/1000000000000) (4445046507/4294967296) (9219789/536870912) 0 8 ![52,0,4] ![(9/64),0,(1/2)] ![(1/64),1,(1/4)] 9435874968362303616672858112000000000000 9780579001096918897997834529902935670784 6373542052039520793504570671104000000000000 raw00463 affine00463
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00463_raw leaf00463_rectangular
    leaf00463_transform leaf00463_sign leaf00463_log
#print axioms leaf00463_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
