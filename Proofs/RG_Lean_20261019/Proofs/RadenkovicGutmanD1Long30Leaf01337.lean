/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01337 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 972665433924501139095552000000000000 982996254859990792904197213287088128 4551433013540887956128006144000000000000))
theorem leaf01337_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 972665433924501139095552000000000000 982996254859990792904197213287088128 4551433013540887956128006144000000000000 raw01337=true := by decide +kernel
#print axioms leaf01337_raw
theorem leaf01337_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01337=true := by decide +kernel
#print axioms leaf01337_rectangular
def affine01337 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01337 (IntegerComputedClassCell.leftNumerator ![(19/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(19/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(19/256),0,0] ![(1/256),1,1]))
theorem leaf01337_transform : affine01337=(NestedInteger.clearedAll 3 raw01337 (IntegerComputedClassCell.leftNumerator ![(19/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(19/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(19/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01337_transform
theorem leaf01337_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01337=true := by decide +kernel
#print axioms leaf01337_sign
theorem leaf01337_log : RationalLog.accepts (542455939/536870912) (11112353/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01337_log
def leaf01337 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (26996889/125000000000) (542455939/536870912) (11112353/2147483648) 0 8 ![60,0,4] ![(19/256),0,0] ![(1/256),1,1] affine01337
theorem leaf01337_checked : FastNestedCellData.accepts 1 2 4 leaf01337=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (26996889/125000000000) (542455939/536870912) (11112353/2147483648) 0 8 ![60,0,4] ![(19/256),0,0] ![(1/256),1,1] 972665433924501139095552000000000000 982996254859990792904197213287088128 4551433013540887956128006144000000000000 raw01337 affine01337
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01337_raw leaf01337_rectangular
    leaf01337_transform leaf01337_sign leaf01337_log
#print axioms leaf01337_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
