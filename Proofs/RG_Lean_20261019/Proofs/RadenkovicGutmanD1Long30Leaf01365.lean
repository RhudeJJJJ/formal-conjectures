/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01365 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 16768090363001982418944000000000000 16768122341317808001314706589483008 18446779253374926294075584806912000000000000))
theorem leaf01365_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 16768090363001982418944000000000000 16768122341317808001314706589483008 18446779253374926294075584806912000000000000 raw01365=true := by decide +kernel
#print axioms leaf01365_raw
theorem leaf01365_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01365=true := by decide +kernel
#print axioms leaf01365_rectangular
def affine01365 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01365 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/2048),1,1]))
theorem leaf01365_transform : affine01365=(NestedInteger.clearedAll 3 raw01365 (IntegerComputedClassCell.leftNumerator ![(1/1024),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/1024),0,0] ![(1/2048),1,1]) (IntegerComputedClassCell.denominator ![(1/1024),0,0] ![(1/2048),1,1])) := by decide +kernel
#print axioms leaf01365_transform
theorem leaf01365_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01365=true := by decide +kernel
#print axioms leaf01365_sign
theorem leaf01365_log : RationalLog.accepts (4294975483/4294967296) (4093/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01365_log
def leaf01365 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) (4093/4294967296) 0 8 ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1] affine01365
theorem leaf01365_checked : FastNestedCellData.accepts 1 2 4 leaf01365=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (909/1000000000000) (4294975483/4294967296) (4093/4294967296) 0 8 ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1] 16768090363001982418944000000000000 16768122341317808001314706589483008 18446779253374926294075584806912000000000000 raw01365 affine01365
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01365_raw leaf01365_rectangular
    leaf01365_transform leaf01365_sign leaf01365_log
#print axioms leaf01365_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
