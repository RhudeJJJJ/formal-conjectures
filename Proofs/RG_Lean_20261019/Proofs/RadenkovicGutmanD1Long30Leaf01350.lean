/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01350 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 5378157458062056628420608000000000000 5384027528815234957110814279169212416 659531358916163624325657657344000000000000))
theorem leaf01350_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 5378157458062056628420608000000000000 5384027528815234957110814279169212416 659531358916163624325657657344000000000000 raw01350=true := by decide +kernel
#print axioms leaf01350_raw
theorem leaf01350_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01350=true := by decide +kernel
#print axioms leaf01350_rectangular
def affine01350 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01350 (IntegerComputedClassCell.leftNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/128),0,0] ![(1/256),1,1]))
theorem leaf01350_transform : affine01350=(NestedInteger.clearedAll 3 raw01350 (IntegerComputedClassCell.leftNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/128),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01350_transform
theorem leaf01350_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01350=true := by decide +kernel
#print axioms leaf01350_sign
theorem leaf01350_log : RationalLog.accepts (4299620003/4294967296) (1162547/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01350_log
def leaf01350 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4081707/500000000000) (4299620003/4294967296) (1162547/2147483648) 0 8 ![60,0,4] ![(3/128),0,0] ![(1/256),1,1] affine01350
theorem leaf01350_checked : FastNestedCellData.accepts 1 2 4 leaf01350=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4081707/500000000000) (4299620003/4294967296) (1162547/2147483648) 0 8 ![60,0,4] ![(3/128),0,0] ![(1/256),1,1] 5378157458062056628420608000000000000 5384027528815234957110814279169212416 659531358916163624325657657344000000000000 raw01350 affine01350
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01350_raw leaf01350_rectangular
    leaf01350_transform leaf01350_sign leaf01350_log
#print axioms leaf01350_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
