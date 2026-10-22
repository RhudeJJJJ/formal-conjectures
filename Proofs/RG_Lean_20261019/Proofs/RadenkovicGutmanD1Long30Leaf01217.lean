/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01217 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 144034190451770061466904821760000000000 163250495725046600998247218736101588992 13938542902443858651308149964800000000000))
theorem leaf01217_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 144034190451770061466904821760000000000 163250495725046600998247218736101588992 13938542902443858651308149964800000000000 raw01217=true := by decide +kernel
#print axioms leaf01217_raw
theorem leaf01217_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01217=true := by decide +kernel
#print axioms leaf01217_rectangular
def affine01217 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01217 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/16),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01217_transform : affine01217=(NestedInteger.clearedAll 3 raw01217 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(5/16),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01217_transform
theorem leaf01217_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01217=true := by decide +kernel
#print axioms leaf01217_sign
theorem leaf01217_log : RationalLog.accepts (2405812665/2147483648) (121967399/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01217_log
def leaf01217 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2342432733/200000000000) (2405812665/2147483648) (121967399/2147483648) 0 8 ![60,0,4] ![(5/16),0,(3/4)] ![(1/64),1,(1/8)] affine01217
theorem leaf01217_checked : FastNestedCellData.accepts 1 2 4 leaf01217=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2342432733/200000000000) (2405812665/2147483648) (121967399/2147483648) 0 8 ![60,0,4] ![(5/16),0,(3/4)] ![(1/64),1,(1/8)] 144034190451770061466904821760000000000 163250495725046600998247218736101588992 13938542902443858651308149964800000000000 raw01217 affine01217
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01217_raw leaf01217_rectangular
    leaf01217_transform leaf01217_sign leaf01217_log
#print axioms leaf01217_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
