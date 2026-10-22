/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00468 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1188209853930378261025521664000000000000 1215188233895993100887732120781148127232 1572131547155694434671115894784000000000000))
theorem leaf00468_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1188209853930378261025521664000000000000 1215188233895993100887732120781148127232 1572131547155694434671115894784000000000000 raw00468=true := by decide +kernel
#print axioms leaf00468_raw
theorem leaf00468_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00468=true := by decide +kernel
#print axioms leaf00468_rectangular
def affine00468 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00468 (IntegerComputedClassCell.leftNumerator ![(7/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf00468_transform : affine00468=(NestedInteger.clearedAll 3 raw00468 (IntegerComputedClassCell.leftNumerator ![(7/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00468_transform
theorem leaf00468_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00468=true := by decide +kernel
#print axioms leaf00468_sign
theorem leaf00468_log : RationalLog.accepts (2194546113/2147483648) (23277093/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00468_log
def leaf00468 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (772955823/1000000000000) (2194546113/2147483648) (23277093/2147483648) 0 8 ![52,0,4] ![(7/64),0,0] ![(1/64),1,(1/2)] affine00468
theorem leaf00468_checked : FastNestedCellData.accepts 1 0 4 leaf00468=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (772955823/1000000000000) (2194546113/2147483648) (23277093/2147483648) 0 8 ![52,0,4] ![(7/64),0,0] ![(1/64),1,(1/2)] 1188209853930378261025521664000000000000 1215188233895993100887732120781148127232 1572131547155694434671115894784000000000000 raw00468 affine00468
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00468_raw leaf00468_rectangular
    leaf00468_transform leaf00468_sign leaf00468_log
#print axioms leaf00468_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
