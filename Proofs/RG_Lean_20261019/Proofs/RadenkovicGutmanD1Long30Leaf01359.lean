/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01359 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 736444751968688001777664000000000000 736495266790299825618445536765935616 4612002346971963514652958130176000000000000))
theorem leaf01359_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 736444751968688001777664000000000000 736495266790299825618445536765935616 4612002346971963514652958130176000000000000 raw01359=true := by decide +kernel
#print axioms leaf01359_raw
theorem leaf01359_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01359=true := by decide +kernel
#print axioms leaf01359_rectangular
def affine01359 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01359 (IntegerComputedClassCell.leftNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(3/512),0,0] ![(1/512),1,1]))
theorem leaf01359_transform : affine01359=(NestedInteger.clearedAll 3 raw01359 (IntegerComputedClassCell.leftNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(3/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01359_transform
theorem leaf01359_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01359=true := by decide +kernel
#print axioms leaf01359_sign
theorem leaf01359_log : RationalLog.accepts (2147630607/2147483648) (146953/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01359_log
def leaf01359 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (159691/1000000000000) (2147630607/2147483648) (146953/4294967296) 0 8 ![60,0,4] ![(3/512),0,0] ![(1/512),1,1] affine01359
theorem leaf01359_checked : FastNestedCellData.accepts 1 2 4 leaf01359=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (159691/1000000000000) (2147630607/2147483648) (146953/4294967296) 0 8 ![60,0,4] ![(3/512),0,0] ![(1/512),1,1] 736444751968688001777664000000000000 736495266790299825618445536765935616 4612002346971963514652958130176000000000000 raw01359 affine01359
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01359_raw leaf01359_rectangular
    leaf01359_transform leaf01359_sign leaf01359_log
#print axioms leaf01359_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
