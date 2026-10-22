/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01257 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 174901693717585037437739991040000000000 186867237991195411813144241140165246976 49271851542938737678720434176000000000000))
theorem leaf01257_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 174901693717585037437739991040000000000 186867237991195411813144241140165246976 49271851542938737678720434176000000000000 raw01257=true := by decide +kernel
#print axioms leaf01257_raw
theorem leaf01257_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01257=true := by decide +kernel
#print axioms leaf01257_rectangular
def affine01257 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01257 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/64),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01257_transform : affine01257=(NestedInteger.clearedAll 3 raw01257 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/64),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01257_transform
theorem leaf01257_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01257=true := by decide +kernel
#print axioms leaf01257_sign
theorem leaf01257_log : RationalLog.accepts (2285730575/2147483648) (66989613/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01257_log
def leaf01257 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1896287963/500000000000) (2285730575/2147483648) (66989613/2147483648) 0 8 ![60,0,4] ![(13/64),0,(3/4)] ![(1/128),1,(1/8)] affine01257
theorem leaf01257_checked : FastNestedCellData.accepts 1 2 4 leaf01257=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1896287963/500000000000) (2285730575/2147483648) (66989613/2147483648) 0 8 ![60,0,4] ![(13/64),0,(3/4)] ![(1/128),1,(1/8)] 174901693717585037437739991040000000000 186867237991195411813144241140165246976 49271851542938737678720434176000000000000 raw01257 affine01257
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01257_raw leaf01257_rectangular
    leaf01257_transform leaf01257_sign leaf01257_log
#print axioms leaf01257_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
