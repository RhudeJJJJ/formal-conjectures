/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01279 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 174294906760137951414321152000000000000 183233866571750679463513255933611343872 75753169251224162607506128896000000000000))
theorem leaf01279_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 174294906760137951414321152000000000000 183233866571750679463513255933611343872 75753169251224162607506128896000000000000 raw01279=true := by decide +kernel
#print axioms leaf01279_raw
theorem leaf01279_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01279=true := by decide +kernel
#print axioms leaf01279_rectangular
def affine01279 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01279 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/64),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01279_transform : affine01279=(NestedInteger.clearedAll 3 raw01279 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/64),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01279_transform
theorem leaf01279_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01279=true := by decide +kernel
#print axioms leaf01279_sign
theorem leaf01279_log : RationalLog.accepts (1126086377/1073741824) (25554335/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01279_log
def leaf01279 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (604706933/250000000000) (1126086377/1073741824) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(15/16)] ![(1/128),1,(1/16)] affine01279
theorem leaf01279_checked : FastNestedCellData.accepts 1 2 4 leaf01279=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (604706933/250000000000) (1126086377/1073741824) (25554335/1073741824) 0 8 ![60,0,4] ![(11/64),0,(15/16)] ![(1/128),1,(1/16)] 174294906760137951414321152000000000000 183233866571750679463513255933611343872 75753169251224162607506128896000000000000 raw01279 affine01279
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01279_raw leaf01279_rectangular
    leaf01279_transform leaf01279_sign leaf01279_log
#print axioms leaf01279_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
