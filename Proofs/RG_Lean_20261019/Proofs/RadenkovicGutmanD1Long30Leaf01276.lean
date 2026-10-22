/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01276 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 537584294508312829097934848000000000000 565155062448860131047008756347340587008 233648329312621975814371540992000000000000))
theorem leaf01276_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 537584294508312829097934848000000000000 565155062448860131047008756347340587008 233648329312621975814371540992000000000000 raw01276=true := by decide +kernel
#print axioms leaf01276_raw
theorem leaf01276_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01276=true := by decide +kernel
#print axioms leaf01276_rectangular
def affine01276 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01276 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/64),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01276_transform : affine01276=(NestedInteger.clearedAll 3 raw01276 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/64),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01276_transform
theorem leaf01276_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01276=true := by decide +kernel
#print axioms leaf01276_sign
theorem leaf01276_log : RationalLog.accepts (4504345509/4294967296) (25554335/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01276_log
def leaf01276 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2418827749/1000000000000) (4504345509/4294967296) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(1/2)] ![(1/128),1,(1/4)] affine01276
theorem leaf01276_checked : FastNestedCellData.accepts 1 2 4 leaf01276=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2418827749/1000000000000) (4504345509/4294967296) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(1/2)] ![(1/128),1,(1/4)] 537584294508312829097934848000000000000 565155062448860131047008756347340587008 233648329312621975814371540992000000000000 raw01276 affine01276
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01276_raw leaf01276_rectangular
    leaf01276_transform leaf01276_sign leaf01276_log
#print axioms leaf01276_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
