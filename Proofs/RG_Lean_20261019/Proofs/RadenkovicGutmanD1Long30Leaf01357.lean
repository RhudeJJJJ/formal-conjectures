/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01357 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2856980993589932653019136000000000000 2857524737605030600899772505917489152 4612563719986361135834624688128000000000000))
theorem leaf01357_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2856980993589932653019136000000000000 2857524737605030600899772505917489152 4612563719986361135834624688128000000000000 raw01357=true := by decide +kernel
#print axioms leaf01357_raw
theorem leaf01357_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01357=true := by decide +kernel
#print axioms leaf01357_rectangular
def affine01357 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01357 (IntegerComputedClassCell.leftNumerator ![(5/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(5/512),0,0] ![(1/512),1,1]))
theorem leaf01357_transform : affine01357=(NestedInteger.clearedAll 3 raw01357 (IntegerComputedClassCell.leftNumerator ![(5/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/512),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(5/512),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01357_transform
theorem leaf01357_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01357=true := by decide +kernel
#print axioms leaf01357_sign
theorem leaf01357_log : RationalLog.accepts (2147891029/2147483648) (203671/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01357_log
def leaf01357 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (619509/1000000000000) (2147891029/2147483648) (203671/2147483648) 0 8 ![60,0,4] ![(5/512),0,0] ![(1/512),1,1] affine01357
theorem leaf01357_checked : FastNestedCellData.accepts 1 2 4 leaf01357=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (619509/1000000000000) (2147891029/2147483648) (203671/2147483648) 0 8 ![60,0,4] ![(5/512),0,0] ![(1/512),1,1] 2856980993589932653019136000000000000 2857524737605030600899772505917489152 4612563719986361135834624688128000000000000 raw01357 affine01357
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01357_raw leaf01357_rectangular
    leaf01357_transform leaf01357_sign leaf01357_log
#print axioms leaf01357_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
