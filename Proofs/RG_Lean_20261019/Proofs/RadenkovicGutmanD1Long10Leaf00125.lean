/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00125 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 9795369981277167595774227251200000000000 8649812227382939804584546576642493906944 162894176278344460284764304179200000000000))
theorem leaf00125_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 9795369981277167595774227251200000000000 8649812227382939804584546576642493906944 162894176278344460284764304179200000000000 raw00125=true := by decide +kernel
#print axioms leaf00125_raw
theorem leaf00125_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00125=true := by decide +kernel
#print axioms leaf00125_rectangular
def affine00125 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00125 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00125_transform : affine00125=(NestedInteger.clearedAll 3 raw00125 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00125_transform
theorem leaf00125_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00125=true := by decide +kernel
#print axioms leaf00125_sign
theorem leaf00125_log : RationalLog.accepts (3601436411/4294967296) (-189097949/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00125_log
def leaf00125 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (5310080707/100000000000) (3601436411/4294967296) (-189097949/2147483648) 1 8 ![52,0,4] ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)] affine00125
theorem leaf00125_checked : FastNestedCellData.accepts 1 0 4 leaf00125=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (5310080707/100000000000) (3601436411/4294967296) (-189097949/2147483648) 1 8 ![52,0,4] ![(23/1600),0,(1/2)] ![(1/1600),1,(1/2)] 9795369981277167595774227251200000000000 8649812227382939804584546576642493906944 162894176278344460284764304179200000000000 raw00125 affine00125
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00125_raw leaf00125_rectangular
    leaf00125_transform leaf00125_sign leaf00125_log
#print axioms leaf00125_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
