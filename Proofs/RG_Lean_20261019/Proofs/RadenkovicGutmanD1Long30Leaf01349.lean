/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01349 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 57783715611248332619382784000000000000 57869417861028577837088098316753829888 4618525867040071987883019337728000000000000))
theorem leaf01349_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 57783715611248332619382784000000000000 57869417861028577837088098316753829888 4618525867040071987883019337728000000000000 raw01349=true := by decide +kernel
#print axioms leaf01349_raw
theorem leaf01349_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01349=true := by decide +kernel
#print axioms leaf01349_rectangular
def affine01349 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01349 (IntegerComputedClassCell.leftNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(7/256),0,0] ![(1/256),1,1]))
theorem leaf01349_transform : affine01349=(NestedInteger.clearedAll 3 raw01349 (IntegerComputedClassCell.leftNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(7/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01349_transform
theorem leaf01349_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01349=true := by decide +kernel
#print axioms leaf01349_sign
theorem leaf01349_log : RationalLog.accepts (4301283507/4294967296) (3155785/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01349_log
def leaf01349 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (6264923/500000000000) (4301283507/4294967296) (3155785/4294967296) 0 8 ![60,0,4] ![(7/256),0,0] ![(1/256),1,1] affine01349
theorem leaf01349_checked : FastNestedCellData.accepts 1 2 4 leaf01349=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (6264923/500000000000) (4301283507/4294967296) (3155785/4294967296) 0 8 ![60,0,4] ![(7/256),0,0] ![(1/256),1,1] 57783715611248332619382784000000000000 57869417861028577837088098316753829888 4618525867040071987883019337728000000000000 raw01349 affine01349
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01349_raw leaf01349_rectangular
    leaf01349_transform leaf01349_sign leaf01349_log
#print axioms leaf01349_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
