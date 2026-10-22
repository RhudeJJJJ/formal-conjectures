/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01255 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 17490170326377509558243295232000000000000 18686724855601940715794858006131966476288 4927185163932460130733744193536000000000000))
theorem leaf01255_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 17490170326377509558243295232000000000000 18686724855601940715794858006131966476288 4927185163932460130733744193536000000000000 raw01255=true := by decide +kernel
#print axioms leaf01255_raw
theorem leaf01255_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01255=true := by decide +kernel
#print axioms leaf01255_rectangular
def affine01255 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01255 (IntegerComputedClassCell.leftNumerator ![(13/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/64),0,0] ![(1/128),1,(1/2)]))
theorem leaf01255_transform : affine01255=(NestedInteger.clearedAll 3 raw01255 (IntegerComputedClassCell.leftNumerator ![(13/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/64),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01255_transform
theorem leaf01255_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01255=true := by decide +kernel
#print axioms leaf01255_sign
theorem leaf01255_log : RationalLog.accepts (2285730579/2147483648) (66989615/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01255_log
def leaf01255 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3792576133/1000000000000) (2285730579/2147483648) (66989615/2147483648) 0 8 ![60,0,4] ![(13/64),0,0] ![(1/128),1,(1/2)] affine01255
theorem leaf01255_checked : FastNestedCellData.accepts 1 2 4 leaf01255=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3792576133/1000000000000) (2285730579/2147483648) (66989615/2147483648) 0 8 ![60,0,4] ![(13/64),0,0] ![(1/128),1,(1/2)] 17490170326377509558243295232000000000000 18686724855601940715794858006131966476288 4927185163932460130733744193536000000000000 raw01255 affine01255
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01255_raw leaf01255_rectangular
    leaf01255_transform leaf01255_sign leaf01255_log
#print axioms leaf01255_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
