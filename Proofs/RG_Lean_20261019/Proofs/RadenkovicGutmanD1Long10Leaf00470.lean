/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00470 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1188209853930378261025521664000000000000 1215188233895993100887732120781148127232 1572131547155694434671115894784000000000000))
theorem leaf00470_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1188209853930378261025521664000000000000 1215188233895993100887732120781148127232 1572131547155694434671115894784000000000000 raw00470=true := by decide +kernel
#print axioms leaf00470_raw
theorem leaf00470_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00470=true := by decide +kernel
#print axioms leaf00470_rectangular
def affine00470 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00470 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/64),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00470_transform : affine00470=(NestedInteger.clearedAll 3 raw00470 (IntegerComputedClassCell.leftNumerator ![(7/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/64),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00470_transform
theorem leaf00470_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00470=true := by decide +kernel
#print axioms leaf00470_sign
theorem leaf00470_log : RationalLog.accepts (2194546113/2147483648) (23277093/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00470_log
def leaf00470 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (772955823/1000000000000) (2194546113/2147483648) (23277093/2147483648) 0 8 ![52,0,4] ![(7/64),0,(3/4)] ![(1/64),1,(1/4)] affine00470
theorem leaf00470_checked : FastNestedCellData.accepts 1 0 4 leaf00470=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (772955823/1000000000000) (2194546113/2147483648) (23277093/2147483648) 0 8 ![52,0,4] ![(7/64),0,(3/4)] ![(1/64),1,(1/4)] 1188209853930378261025521664000000000000 1215188233895993100887732120781148127232 1572131547155694434671115894784000000000000 raw00470 affine00470
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00470_raw leaf00470_rectangular
    leaf00470_transform leaf00470_sign leaf00470_log
#print axioms leaf00470_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
