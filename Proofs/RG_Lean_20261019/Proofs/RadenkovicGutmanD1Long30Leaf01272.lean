/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01272 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 196641850040634773690384384000000000000 207543994159744287823829665332332593152 76052584295166877305623543808000000000000))
theorem leaf01272_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 196641850040634773690384384000000000000 207543994159744287823829665332332593152 76052584295166877305623543808000000000000 raw01272=true := by decide +kernel
#print axioms leaf01272_raw
theorem leaf01272_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01272=true := by decide +kernel
#print axioms leaf01272_rectangular
def affine01272 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01272 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/128),0,(3/4)] ![(1/128),1,(1/8)]))
theorem leaf01272_transform : affine01272=(NestedInteger.clearedAll 3 raw01272 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(3/4)] ![(1/128),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/128),0,(3/4)] ![(1/128),1,(1/8)])) := by decide +kernel
#print axioms leaf01272_transform
theorem leaf01272_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01272=true := by decide +kernel
#print axioms leaf01272_sign
theorem leaf01272_log : RationalLog.accepts (282546897/268435456) (27506069/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01272_log
def leaf01272 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (2728953869/1000000000000) (282546897/268435456) (27506069/1073741824) 0 8 ![60,0,4] ![(23/128),0,(3/4)] ![(1/128),1,(1/8)] affine01272
theorem leaf01272_checked : FastNestedCellData.accepts 1 2 4 leaf01272=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (2728953869/1000000000000) (282546897/268435456) (27506069/1073741824) 0 8 ![60,0,4] ![(23/128),0,(3/4)] ![(1/128),1,(1/8)] 196641850040634773690384384000000000000 207543994159744287823829665332332593152 76052584295166877305623543808000000000000 raw01272 affine01272
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01272_raw leaf01272_rectangular
    leaf01272_transform leaf01272_sign leaf01272_log
#print axioms leaf01272_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
