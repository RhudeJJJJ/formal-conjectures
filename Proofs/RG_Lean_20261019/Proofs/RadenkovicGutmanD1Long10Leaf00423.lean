/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00423 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 38059908227634269854208360448000000000000 46061469234222353875041019079078273089536 1860409404958867317603671474176000000000000))
theorem leaf00423_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 38059908227634269854208360448000000000000 46061469234222353875041019079078273089536 1860409404958867317603671474176000000000000 raw00423=true := by decide +kernel
#print axioms leaf00423_raw
theorem leaf00423_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00423=true := by decide +kernel
#print axioms leaf00423_rectangular
def affine00423 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00423 (IntegerComputedClassCell.leftNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf00423_transform : affine00423=(NestedInteger.clearedAll 3 raw00423 (IntegerComputedClassCell.leftNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf00423_transform
theorem leaf00423_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00423=true := by decide +kernel
#print axioms leaf00423_sign
theorem leaf00423_log : RationalLog.accepts (2536169451/2147483648) (178625641/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00423_log
def leaf00423 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (24758781111/1000000000000) (2536169451/2147483648) (178625641/2147483648) 0 8 ![52,0,4] ![(13/32),0,0] ![(1/32),1,(1/2)] affine00423
theorem leaf00423_checked : FastNestedCellData.accepts 1 0 4 leaf00423=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (24758781111/1000000000000) (2536169451/2147483648) (178625641/2147483648) 0 8 ![52,0,4] ![(13/32),0,0] ![(1/32),1,(1/2)] 38059908227634269854208360448000000000000 46061469234222353875041019079078273089536 1860409404958867317603671474176000000000000 raw00423 affine00423
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00423_raw leaf00423_rectangular
    leaf00423_transform leaf00423_sign leaf00423_log
#print axioms leaf00423_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
