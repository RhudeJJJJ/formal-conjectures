/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00480 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 3119223827274903302071910400000000000 3156089344279935321847040419358048256 11665476660133797757878429286400000000000))
theorem leaf00480_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 3119223827274903302071910400000000000 3156089344279935321847040419358048256 11665476660133797757878429286400000000000 raw00480=true := by decide +kernel
#print axioms leaf00480_raw
theorem leaf00480_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00480=true := by decide +kernel
#print axioms leaf00480_rectangular
def affine00480 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00480 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/128),1,(1/2)]))
theorem leaf00480_transform : affine00480=(NestedInteger.clearedAll 3 raw00480 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf00480_transform
theorem leaf00480_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00480=true := by decide +kernel
#print axioms leaf00480_sign
theorem leaf00480_log : RationalLog.accepts (2172276643/2147483648) (24650967/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00480_log
def leaf00480 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (13527477/50000000000) (2172276643/2147483648) (24650967/4294967296) 0 8 ![52,0,4] ![(5/64),0,0] ![(1/128),1,(1/2)] affine00480
theorem leaf00480_checked : FastNestedCellData.accepts 1 0 4 leaf00480=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (13527477/50000000000) (2172276643/2147483648) (24650967/4294967296) 0 8 ![52,0,4] ![(5/64),0,0] ![(1/128),1,(1/2)] 3119223827274903302071910400000000000 3156089344279935321847040419358048256 11665476660133797757878429286400000000000 raw00480 affine00480
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00480_raw leaf00480_rectangular
    leaf00480_transform leaf00480_sign leaf00480_log
#print axioms leaf00480_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
