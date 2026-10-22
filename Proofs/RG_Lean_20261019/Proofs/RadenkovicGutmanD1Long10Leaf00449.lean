/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00449 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 363770139298234116073324544000000000000 393260848235503097689168289474084339712 77899276196314863279777251328000000000000))
theorem leaf00449_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 363770139298234116073324544000000000000 393260848235503097689168289474084339712 77899276196314863279777251328000000000000 raw00449=true := by decide +kernel
#print axioms leaf00449_raw
theorem leaf00449_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00449=true := by decide +kernel
#print axioms leaf00449_rectangular
def affine00449 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00449 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00449_transform : affine00449=(NestedInteger.clearedAll 3 raw00449 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00449_transform
theorem leaf00449_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00449=true := by decide +kernel
#print axioms leaf00449_sign
theorem leaf00449_log : RationalLog.accepts (1154959063/1073741824) (156584457/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00449_log
def leaf00449 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1262081201/250000000000) (1154959063/1073741824) (156584457/4294967296) 0 8 ![52,0,4] ![(7/32),0,(3/4)] ![(1/64),1,(1/4)] affine00449
theorem leaf00449_checked : FastNestedCellData.accepts 1 0 4 leaf00449=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1262081201/250000000000) (1154959063/1073741824) (156584457/4294967296) 0 8 ![52,0,4] ![(7/32),0,(3/4)] ![(1/64),1,(1/4)] 363770139298234116073324544000000000000 393260848235503097689168289474084339712 77899276196314863279777251328000000000000 raw00449 affine00449
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00449_raw leaf00449_rectangular
    leaf00449_transform leaf00449_sign leaf00449_log
#print axioms leaf00449_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
