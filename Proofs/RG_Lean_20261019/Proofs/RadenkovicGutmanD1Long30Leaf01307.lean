/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01307 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 741189671440862164289165721600000000000 762507401363300461076878504754814124032 759092007308437498612807421132800000000000))
theorem leaf01307_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 741189671440862164289165721600000000000 762507401363300461076878504754814124032 759092007308437498612807421132800000000000 raw01307=true := by decide +kernel
#print axioms leaf01307_raw
theorem leaf01307_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01307=true := by decide +kernel
#print axioms leaf01307_rectangular
def affine01307 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01307 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/8),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01307_transform : affine01307=(NestedInteger.clearedAll 3 raw01307 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/8),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01307_transform
theorem leaf01307_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01307=true := by decide +kernel
#print axioms leaf01307_sign
theorem leaf01307_log : RationalLog.accepts (4414063093/4294967296) (58737243/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01307_log
def leaf01307 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (200899863/200000000000) (4414063093/4294967296) (58737243/4294967296) 0 8 ![60,0,4] ![(1/8),0,(3/4)] ![(1/128),1,(1/8)] affine01307
theorem leaf01307_checked : FastNestedCellData.accepts 1 2 4 leaf01307=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (200899863/200000000000) (4414063093/4294967296) (58737243/4294967296) 0 8 ![60,0,4] ![(1/8),0,(3/4)] ![(1/128),1,(1/8)] 741189671440862164289165721600000000000 762507401363300461076878504754814124032 759092007308437498612807421132800000000000 raw01307 affine01307
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01307_raw leaf01307_rectangular
    leaf01307_transform leaf01307_sign leaf01307_log
#print axioms leaf01307_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
