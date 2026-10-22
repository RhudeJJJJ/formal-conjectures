/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01362 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 5754231229492773257216000000000000 5754329958846944373159237242585088 288235321521085171967503368192000000000000))
theorem leaf01362_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 5754231229492773257216000000000000 5754329958846944373159237242585088 288235321521085171967503368192000000000000 raw01362=true := by decide +kernel
#print axioms leaf01362_raw
theorem leaf01362_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01362=true := by decide +kernel
#print axioms leaf01362_rectangular
def affine01362 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01362 (IntegerComputedClassCell.leftNumerator ![(3/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(3/1024),0,0] ![(1/1024),1,1]))
theorem leaf01362_transform : affine01362=(NestedInteger.clearedAll 3 raw01362 (IntegerComputedClassCell.leftNumerator ![(3/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/1024),0,0] ![(1/1024),1,1]) (IntegerComputedClassCell.denominator ![(3/1024),0,0] ![(1/1024),1,1])) := by decide +kernel
#print axioms leaf01362_transform
theorem leaf01362_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01362=true := by decide +kernel
#print axioms leaf01362_sign
theorem leaf01362_log : RationalLog.accepts (2147520451/2147483648) (18401/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01362_log
def leaf01362 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4991/250000000000) (2147520451/2147483648) (18401/2147483648) 0 8 ![60,0,4] ![(3/1024),0,0] ![(1/1024),1,1] affine01362
theorem leaf01362_checked : FastNestedCellData.accepts 1 2 4 leaf01362=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4991/250000000000) (2147520451/2147483648) (18401/2147483648) 0 8 ![60,0,4] ![(3/1024),0,0] ![(1/1024),1,1] 5754231229492773257216000000000000 5754329958846944373159237242585088 288235321521085171967503368192000000000000 raw01362 affine01362
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01362_raw leaf01362_rectangular
    leaf01362_transform leaf01362_sign leaf01362_log
#print axioms leaf01362_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
