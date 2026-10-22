/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01227 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1676218872384059663265982054400000000000 1868737465249468064532233240616005271552 205654060638158065352953351372800000000000))
theorem leaf01227_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1676218872384059663265982054400000000000 1868737465249468064532233240616005271552 205654060638158065352953351372800000000000 raw01227=true := by decide +kernel
#print axioms leaf01227_raw
theorem leaf01227_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01227=true := by decide +kernel
#print axioms leaf01227_rectangular
def affine01227 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01227 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/32),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01227_transform : affine01227=(NestedInteger.clearedAll 3 raw01227 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/32),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01227_transform
theorem leaf01227_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01227=true := by decide +kernel
#print axioms leaf01227_sign
theorem leaf01227_log : RationalLog.accepts (2372569301/2147483648) (214054085/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01227_log
def leaf01227 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1817360143/200000000000) (2372569301/2147483648) (214054085/4294967296) 0 8 ![60,0,4] ![(9/32),0,(3/4)] ![(1/64),1,(1/8)] affine01227
theorem leaf01227_checked : FastNestedCellData.accepts 1 2 4 leaf01227=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1817360143/200000000000) (2372569301/2147483648) (214054085/4294967296) 0 8 ![60,0,4] ![(9/32),0,(3/4)] ![(1/64),1,(1/8)] 1676218872384059663265982054400000000000 1868737465249468064532233240616005271552 205654060638158065352953351372800000000000 raw01227 affine01227
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01227_raw leaf01227_rectangular
    leaf01227_transform leaf01227_sign leaf01227_log
#print axioms leaf01227_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
