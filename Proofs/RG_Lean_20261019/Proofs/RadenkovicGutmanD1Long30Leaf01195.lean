/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01195 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1794047984649288959947440128000000000000 2098064860401714741589127126376347860992 112357831577637582144821788672000000000000))
theorem leaf01195_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1794047984649288959947440128000000000000 2098064860401714741589127126376347860992 112357831577637582144821788672000000000000 raw01195=true := by decide +kernel
#print axioms leaf01195_raw
theorem leaf01195_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01195=true := by decide +kernel
#print axioms leaf01195_rectangular
def affine01195 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01195 (IntegerComputedClassCell.leftNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/8),0,0] ![(1/32),1,(1/2)]))
theorem leaf01195_transform : affine01195=(NestedInteger.clearedAll 3 raw01195 (IntegerComputedClassCell.leftNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/8),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01195_transform
theorem leaf01195_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01195=true := by decide +kernel
#print axioms leaf01195_sign
theorem leaf01195_log : RationalLog.accepts (4930714929/4294967296) (296438755/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01195_log
def leaf01195 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2334132867/125000000000) (4930714929/4294967296) (296438755/4294967296) 0 8 ![60,0,4] ![(3/8),0,0] ![(1/32),1,(1/2)] affine01195
theorem leaf01195_checked : FastNestedCellData.accepts 1 2 4 leaf01195=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2334132867/125000000000) (4930714929/4294967296) (296438755/4294967296) 0 8 ![60,0,4] ![(3/8),0,0] ![(1/32),1,(1/2)] 1794047984649288959947440128000000000000 2098064860401714741589127126376347860992 112357831577637582144821788672000000000000 raw01195 affine01195
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01195_raw leaf01195_rectangular
    leaf01195_transform leaf01195_sign leaf01195_log
#print axioms leaf01195_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
