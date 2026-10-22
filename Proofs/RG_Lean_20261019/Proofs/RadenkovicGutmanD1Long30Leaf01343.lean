/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01343 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 445911724094487315578093568000000000000 448164967757032564202914009132138758144 6179985870375606681946214629376000000000000))
theorem leaf01343_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 445911724094487315578093568000000000000 448164967757032564202914009132138758144 6179985870375606681946214629376000000000000 raw01343=true := by decide +kernel
#print axioms leaf01343_raw
theorem leaf01343_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01343=true := by decide +kernel
#print axioms leaf01343_rectangular
def affine01343 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01343 (IntegerComputedClassCell.leftNumerator ![(13/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(13/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(13/256),0,0] ![(1/256),1,1]))
theorem leaf01343_transform : affine01343=(NestedInteger.clearedAll 3 raw01343 (IntegerComputedClassCell.leftNumerator ![(13/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(13/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(13/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01343_transform
theorem leaf01343_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01343=true := by decide +kernel
#print axioms leaf01343_sign
theorem leaf01343_log : RationalLog.accepts (4316357247/4294967296) (10668431/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01343_log
def leaf01343 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (72518769/1000000000000) (4316357247/4294967296) (10668431/4294967296) 0 8 ![60,0,4] ![(13/256),0,0] ![(1/256),1,1] affine01343
theorem leaf01343_checked : FastNestedCellData.accepts 1 2 4 leaf01343=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (72518769/1000000000000) (4316357247/4294967296) (10668431/4294967296) 0 8 ![60,0,4] ![(13/256),0,0] ![(1/256),1,1] 445911724094487315578093568000000000000 448164967757032564202914009132138758144 6179985870375606681946214629376000000000000 raw01343 affine01343
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01343_raw leaf01343_rectangular
    leaf01343_transform leaf01343_sign leaf01343_log
#print axioms leaf01343_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
