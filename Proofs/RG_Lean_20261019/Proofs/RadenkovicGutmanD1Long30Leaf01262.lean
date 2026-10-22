/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01262 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 15752067763199704470044803072000000000000 16760418683862408788831502027306204921856 4906897917740852192554560520192000000000000))
theorem leaf01262_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 15752067763199704470044803072000000000000 16760418683862408788831502027306204921856 4906897917740852192554560520192000000000000 raw01262=true := by decide +kernel
#print axioms leaf01262_raw
theorem leaf01262_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01262=true := by decide +kernel
#print axioms leaf01262_rectangular
def affine01262 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01262 (IntegerComputedClassCell.leftNumerator ![(25/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(25/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01262_transform : affine01262=(NestedInteger.clearedAll 3 raw01262 (IntegerComputedClassCell.leftNumerator ![(25/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(25/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01262_transform
theorem leaf01262_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01262=true := by decide +kernel
#print axioms leaf01262_sign
theorem leaf01262_log : RationalLog.accepts (4554348581/4294967296) (125925365/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01262_log
def leaf01262 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1707842609/500000000000) (4554348581/4294967296) (125925365/4294967296) 0 8 ![60,0,4] ![(25/128),0,(3/4)] ![(1/128),1,(1/8)] affine01262
theorem leaf01262_checked : FastNestedCellData.accepts 1 2 4 leaf01262=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1707842609/500000000000) (4554348581/4294967296) (125925365/4294967296) 0 8 ![60,0,4] ![(25/128),0,(3/4)] ![(1/128),1,(1/8)] 15752067763199704470044803072000000000000 16760418683862408788831502027306204921856 4906897917740852192554560520192000000000000 raw01262 affine01262
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01262_raw leaf01262_rectangular
    leaf01262_transform leaf01262_sign leaf01262_log
#print axioms leaf01262_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
