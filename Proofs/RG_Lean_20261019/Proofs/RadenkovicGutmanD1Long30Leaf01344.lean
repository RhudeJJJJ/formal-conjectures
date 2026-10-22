/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01344 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 10636044727307697299642122240000000000 10681945548384242875754752133486870528 185263526801869427705435389952000000000000))
theorem leaf01344_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 10636044727307697299642122240000000000 10681945548384242875754752133486870528 185263526801869427705435389952000000000000 raw01344=true := by decide +kernel
#print axioms leaf01344_raw
theorem leaf01344_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01344=true := by decide +kernel
#print axioms leaf01344_rectangular
def affine01344 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01344 (IntegerComputedClassCell.leftNumerator ![(3/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/64),0,0] ![(1/256),1,1]))
theorem leaf01344_transform : affine01344=(NestedInteger.clearedAll 3 raw01344 (IntegerComputedClassCell.leftNumerator ![(3/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/64),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01344_transform
theorem leaf01344_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01344=true := by decide +kernel
#print axioms leaf01344_sign
theorem leaf01344_log : RationalLog.accepts (4313253925/4294967296) (142561/67108864) 0 8=true := by decide +kernel
#print axioms leaf01344_log
def leaf01344 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (28829057/500000000000) (4313253925/4294967296) (142561/67108864) 0 8 ![60,0,4] ![(3/64),0,0] ![(1/256),1,1] affine01344
theorem leaf01344_checked : FastNestedCellData.accepts 1 2 4 leaf01344=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (28829057/500000000000) (4313253925/4294967296) (142561/67108864) 0 8 ![60,0,4] ![(3/64),0,0] ![(1/256),1,1] 10636044727307697299642122240000000000 10681945548384242875754752133486870528 185263526801869427705435389952000000000000 raw01344 affine01344
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01344_raw leaf01344_rectangular
    leaf01344_transform leaf01344_sign leaf01344_log
#print axioms leaf01344_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
