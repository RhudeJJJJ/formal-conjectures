/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01077 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1472347973653726023331770007552000000000000 1534114223910470432721454585114634731126784 4805150170799500213234505351168000000000000))
theorem leaf01077_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1472347973653726023331770007552000000000000 1534114223910470432721454585114634731126784 4805150170799500213234505351168000000000000 raw01077=true := by decide +kernel
#print axioms leaf01077_raw
theorem leaf01077_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01077=true := by decide +kernel
#print axioms leaf01077_rectangular
def affine01077 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01077 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01077_transform : affine01077=(NestedInteger.clearedAll 3 raw01077 (IntegerComputedClassCell.leftNumerator ![(59/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(59/160),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01077_transform
theorem leaf01077_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01077=true := by decide +kernel
#print axioms leaf01077_sign
theorem leaf01077_log : RationalLog.accepts (3392151139/4294967296) (-506762511/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01077_log
def leaf01077 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (159632287169/500000000000) (3392151139/4294967296) (-506762511/4294967296) 1 8 ![60,0,4] ![(59/160),0,(1/8)] ![(3/160),1,(1/8)] affine01077
theorem leaf01077_checked : FastNestedCellData.accepts 1 2 4 leaf01077=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (159632287169/500000000000) (3392151139/4294967296) (-506762511/4294967296) 1 8 ![60,0,4] ![(59/160),0,(1/8)] ![(3/160),1,(1/8)] 1472347973653726023331770007552000000000000 1534114223910470432721454585114634731126784 4805150170799500213234505351168000000000000 raw01077 affine01077
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01077_raw leaf01077_rectangular
    leaf01077_transform leaf01077_sign leaf01077_log
#print axioms leaf01077_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
