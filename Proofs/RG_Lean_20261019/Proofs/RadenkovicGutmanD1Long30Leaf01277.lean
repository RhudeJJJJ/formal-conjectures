/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01277 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 14873165419907508026011025408000000000000 15635956662953110243426195076692152680448 6464270444251387942027481055232000000000000))
theorem leaf01277_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 14873165419907508026011025408000000000000 15635956662953110243426195076692152680448 6464270444251387942027481055232000000000000 raw01277=true := by decide +kernel
#print axioms leaf01277_raw
theorem leaf01277_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01277=true := by decide +kernel
#print axioms leaf01277_rectangular
def affine01277 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01277 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/64),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01277_transform : affine01277=(NestedInteger.clearedAll 3 raw01277 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/64),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01277_transform
theorem leaf01277_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01277=true := by decide +kernel
#print axioms leaf01277_sign
theorem leaf01277_log : RationalLog.accepts (4504345509/4294967296) (25554335/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01277_log
def leaf01277 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2418827739/1000000000000) (4504345509/4294967296) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(3/4)] ![(1/128),1,(1/8)] affine01277
theorem leaf01277_checked : FastNestedCellData.accepts 1 2 4 leaf01277=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2418827739/1000000000000) (4504345509/4294967296) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(3/4)] ![(1/128),1,(1/8)] 14873165419907508026011025408000000000000 15635956662953110243426195076692152680448 6464270444251387942027481055232000000000000 raw01277 affine01277
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01277_raw leaf01277_rectangular
    leaf01277_transform leaf01277_sign leaf01277_log
#print axioms leaf01277_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
