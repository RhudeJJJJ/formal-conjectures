/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01222 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1911131847531603187058134220800000000000 2148459454144150483448006908004781785088 207374921591763674755778582937600000000000))
theorem leaf01222_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1911131847531603187058134220800000000000 2148459454144150483448006908004781785088 207374921591763674755778582937600000000000 raw01222=true := by decide +kernel
#print axioms leaf01222_raw
theorem leaf01222_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01222=true := by decide +kernel
#print axioms leaf01222_rectangular
def affine01222 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01222 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/64),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01222_transform : affine01222=(NestedInteger.clearedAll 3 raw01222 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/64),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01222_transform
theorem leaf01222_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01222=true := by decide +kernel
#print axioms leaf01222_sign
theorem leaf01222_log : RationalLog.accepts (2389406931/2147483648) (229240505/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01222_log
def leaf01222 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2072053301/200000000000) (2389406931/2147483648) (229240505/4294967296) 0 8 ![60,0,4] ![(19/64),0,(3/4)] ![(1/64),1,(1/8)] affine01222
theorem leaf01222_checked : FastNestedCellData.accepts 1 2 4 leaf01222=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2072053301/200000000000) (2389406931/2147483648) (229240505/4294967296) 0 8 ![60,0,4] ![(19/64),0,(3/4)] ![(1/64),1,(1/8)] 1911131847531603187058134220800000000000 2148459454144150483448006908004781785088 207374921591763674755778582937600000000000 raw01222 affine01222
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01222_raw leaf01222_rectangular
    leaf01222_transform leaf01222_sign leaf01222_log
#print axioms leaf01222_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
