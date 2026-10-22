/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00454 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 3858264435045602831730999296000000000000 4096884877693037912496521120410201227264 1224225751477054308877948944384000000000000))
theorem leaf00454_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 3858264435045602831730999296000000000000 4096884877693037912496521120410201227264 1224225751477054308877948944384000000000000 raw00454=true := by decide +kernel
#print axioms leaf00454_raw
theorem leaf00454_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00454=true := by decide +kernel
#print axioms leaf00454_rectangular
def affine00454 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00454 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00454_transform : affine00454=(NestedInteger.clearedAll 3 raw00454 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00454_transform
theorem leaf00454_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00454=true := by decide +kernel
#print axioms leaf00454_sign
theorem leaf00454_log : RationalLog.accepts (2272692567/2147483648) (60847361/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00454_log
def leaf00454 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1673255473/500000000000) (2272692567/2147483648) (60847361/2147483648) 0 8 ![52,0,4] ![(3/16),0,(1/2)] ![(1/64),1,(1/4)] affine00454
theorem leaf00454_checked : FastNestedCellData.accepts 1 0 4 leaf00454=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1673255473/500000000000) (2272692567/2147483648) (60847361/2147483648) 0 8 ![52,0,4] ![(3/16),0,(1/2)] ![(1/64),1,(1/4)] 3858264435045602831730999296000000000000 4096884877693037912496521120410201227264 1224225751477054308877948944384000000000000 raw00454 affine00454
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00454_raw leaf00454_rectangular
    leaf00454_transform leaf00454_sign leaf00454_log
#print axioms leaf00454_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
