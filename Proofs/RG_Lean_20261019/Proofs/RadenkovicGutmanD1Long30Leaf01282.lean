/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01282 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 39302070832706900669302308864000000000000 41158329932866008911187586419491472408576 19317994260522444987613256351744000000000000))
theorem leaf01282_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 39302070832706900669302308864000000000000 41158329932866008911187586419491472408576 19317994260522444987613256351744000000000000 raw01282=true := by decide +kernel
#print axioms leaf01282_raw
theorem leaf01282_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01282=true := by decide +kernel
#print axioms leaf01282_rectangular
def affine01282 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01282 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01282_transform : affine01282=(NestedInteger.clearedAll 3 raw01282 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01282_transform
theorem leaf01282_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01282=true := by decide +kernel
#print axioms leaf01282_sign
theorem leaf01282_log : RationalLog.accepts (4488258491/4294967296) (47266997/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01282_log
def leaf01282 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2130569529/1000000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(3/4)] ![(1/128),1,(1/8)] affine01282
theorem leaf01282_checked : FastNestedCellData.accepts 1 2 4 leaf01282=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2130569529/1000000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(3/4)] ![(1/128),1,(1/8)] 39302070832706900669302308864000000000000 41158329932866008911187586419491472408576 19317994260522444987613256351744000000000000 raw01282 affine01282
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01282_raw leaf01282_rectangular
    leaf01282_transform leaf01282_sign leaf01282_log
#print axioms leaf01282_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
