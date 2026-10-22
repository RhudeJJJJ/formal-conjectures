/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01285 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2148908205615267424403193856000000000000 2241919923959834597978850433439035817984 1202823687482631318062093041664000000000000))
theorem leaf01285_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2148908205615267424403193856000000000000 2241919923959834597978850433439035817984 1202823687482631318062093041664000000000000 raw01285=true := by decide +kernel
#print axioms leaf01285_raw
theorem leaf01285_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01285=true := by decide +kernel
#print axioms leaf01285_rectangular
def affine01285 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01285 (IntegerComputedClassCell.leftNumerator ![(5/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/32),0,0] ![(1/128),1,(1/2)]))
theorem leaf01285_transform : affine01285=(NestedInteger.clearedAll 3 raw01285 (IntegerComputedClassCell.leftNumerator ![(5/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/32),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01285_transform
theorem leaf01285_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01285=true := by decide +kernel
#print axioms leaf01285_sign
theorem leaf01285_log : RationalLog.accepts (4472531149/4294967296) (86995765/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01285_log
def leaf01285 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (465970189/250000000000) (4472531149/4294967296) (86995765/4294967296) 0 8 ![60,0,4] ![(5/32),0,0] ![(1/128),1,(1/2)] affine01285
theorem leaf01285_checked : FastNestedCellData.accepts 1 2 4 leaf01285=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (465970189/250000000000) (4472531149/4294967296) (86995765/4294967296) 0 8 ![60,0,4] ![(5/32),0,0] ![(1/128),1,(1/2)] 2148908205615267424403193856000000000000 2241919923959834597978850433439035817984 1202823687482631318062093041664000000000000 raw01285 affine01285
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01285_raw leaf01285_rectangular
    leaf01285_transform leaf01285_sign leaf01285_log
#print axioms leaf01285_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
