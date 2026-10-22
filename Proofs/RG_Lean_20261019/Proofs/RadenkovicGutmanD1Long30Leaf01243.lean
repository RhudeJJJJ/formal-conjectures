/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01243 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 5318122593115435946984289075200000000000 5779677363476586787508115213813144354816 1002385966907614928906867441664000000000000))
theorem leaf01243_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 5318122593115435946984289075200000000000 5779677363476586787508115213813144354816 1002385966907614928906867441664000000000000 raw01243=true := by decide +kernel
#print axioms leaf01243_raw
theorem leaf01243_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01243=true := by decide +kernel
#print axioms leaf01243_rectangular
def affine01243 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01243 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/64),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01243_transform : affine01243=(NestedInteger.clearedAll 3 raw01243 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/64),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01243_transform
theorem leaf01243_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01243=true := by decide +kernel
#print axioms leaf01243_sign
theorem leaf01243_log : RationalLog.accepts (2320481985/2147483648) (5199471/134217728) 0 8=true := by decide +kernel
#print axioms leaf01243_log
def leaf01243 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (5765920069/1000000000000) (2320481985/2147483648) (5199471/134217728) 0 8 ![60,0,4] ![(15/64),0,(7/8)] ![(1/64),1,(1/16)] affine01243
theorem leaf01243_checked : FastNestedCellData.accepts 1 2 4 leaf01243=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (5765920069/1000000000000) (2320481985/2147483648) (5199471/134217728) 0 8 ![60,0,4] ![(15/64),0,(7/8)] ![(1/64),1,(1/16)] 5318122593115435946984289075200000000000 5779677363476586787508115213813144354816 1002385966907614928906867441664000000000000 raw01243 affine01243
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01243_raw leaf01243_rectangular
    leaf01243_transform leaf01243_sign leaf01243_log
#print axioms leaf01243_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
