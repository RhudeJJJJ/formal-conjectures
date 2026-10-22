/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01187 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 298217512799092672577090355200000000000 358083264270511287963538792403838173184 13843650292108034622472008499200000000000))
theorem leaf01187_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 298217512799092672577090355200000000000 358083264270511287963538792403838173184 13843650292108034622472008499200000000000 raw01187=true := by decide +kernel
#print axioms leaf01187_raw
theorem leaf01187_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01187=true := by decide +kernel
#print axioms leaf01187_rectangular
def affine01187 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01187 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/16),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01187_transform : affine01187=(NestedInteger.clearedAll 3 raw01187 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/16),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01187_transform
theorem leaf01187_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01187=true := by decide +kernel
#print axioms leaf01187_sign
theorem leaf01187_log : RationalLog.accepts (2513564333/2147483648) (169012373/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01187_log
def leaf01187 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1293312301/50000000000) (2513564333/2147483648) (169012373/2147483648) 0 8 ![60,0,4] ![(7/16),0,(3/4)] ![(1/32),1,(1/8)] affine01187
theorem leaf01187_checked : FastNestedCellData.accepts 1 2 4 leaf01187=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1293312301/50000000000) (2513564333/2147483648) (169012373/2147483648) 0 8 ![60,0,4] ![(7/16),0,(3/4)] ![(1/32),1,(1/8)] 298217512799092672577090355200000000000 358083264270511287963538792403838173184 13843650292108034622472008499200000000000 raw01187 affine01187
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01187_raw leaf01187_rectangular
    leaf01187_transform leaf01187_sign leaf01187_log
#print axioms leaf01187_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
