/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00481 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 3119223827274903302071910400000000000 3156089344279935321847040419358048256 11665476660133797757878429286400000000000))
theorem leaf00481_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 3119223827274903302071910400000000000 3156089344279935321847040419358048256 11665476660133797757878429286400000000000 raw00481=true := by decide +kernel
#print axioms leaf00481_raw
theorem leaf00481_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00481=true := by decide +kernel
#print axioms leaf00481_rectangular
def affine00481 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00481 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf00481_transform : affine00481=(NestedInteger.clearedAll 3 raw00481 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00481_transform
theorem leaf00481_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00481=true := by decide +kernel
#print axioms leaf00481_sign
theorem leaf00481_log : RationalLog.accepts (2172276643/2147483648) (24650967/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00481_log
def leaf00481 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (13527477/50000000000) (2172276643/2147483648) (24650967/4294967296) 0 8 ![52,0,4] ![(5/64),0,(1/2)] ![(1/128),1,(1/4)] affine00481
theorem leaf00481_checked : FastNestedCellData.accepts 1 0 4 leaf00481=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (13527477/50000000000) (2172276643/2147483648) (24650967/4294967296) 0 8 ![52,0,4] ![(5/64),0,(1/2)] ![(1/128),1,(1/4)] 3119223827274903302071910400000000000 3156089344279935321847040419358048256 11665476660133797757878429286400000000000 raw00481 affine00481
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00481_raw leaf00481_rectangular
    leaf00481_transform leaf00481_sign leaf00481_log
#print axioms leaf00481_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
