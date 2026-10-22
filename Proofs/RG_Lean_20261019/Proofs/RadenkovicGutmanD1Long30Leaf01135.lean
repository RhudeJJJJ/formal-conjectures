/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01135 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1311052623919191372595200000000000 1664509922483621575790349835567104 13959378753602755179315200000000000))
theorem leaf01135_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1311052623919191372595200000000000 1664509922483621575790349835567104 13959378753602755179315200000000000 raw01135=true := by decide +kernel
#print axioms leaf01135_raw
theorem leaf01135_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01135=true := by decide +kernel
#print axioms leaf01135_rectangular
def affine01135 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01135 (IntegerComputedClassCell.leftNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/8),0,0] ![(1/16),1,(1/2)]))
theorem leaf01135_transform : affine01135=(NestedInteger.clearedAll 3 raw01135 (IntegerComputedClassCell.leftNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/8),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01135_transform
theorem leaf01135_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01135=true := by decide +kernel
#print axioms leaf01135_sign
theorem leaf01135_log : RationalLog.accepts (9515533/8388608) (270692291/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01135_log
def leaf01135 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1490494269/12500000000) (9515533/8388608) (270692291/4294967296) 0 8 ![60,0,4] ![(7/8),0,0] ![(1/16),1,(1/2)] affine01135
theorem leaf01135_checked : FastNestedCellData.accepts 1 2 4 leaf01135=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1490494269/12500000000) (9515533/8388608) (270692291/4294967296) 0 8 ![60,0,4] ![(7/8),0,0] ![(1/16),1,(1/2)] 1311052623919191372595200000000000 1664509922483621575790349835567104 13959378753602755179315200000000000 raw01135 affine01135
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01135_raw leaf01135_rectangular
    leaf01135_transform leaf01135_sign leaf01135_log
#print axioms leaf01135_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
