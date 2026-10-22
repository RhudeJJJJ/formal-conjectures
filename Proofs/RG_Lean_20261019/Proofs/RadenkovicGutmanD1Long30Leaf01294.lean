/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01294 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1865884348038462401901756416000000000000 1939500182401509464632892088192161808384 1198408395906383785749406285824000000000000))
theorem leaf01294_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1865884348038462401901756416000000000000 1939500182401509464632892088192161808384 1198408395906383785749406285824000000000000 raw01294=true := by decide +kernel
#print axioms leaf01294_raw
theorem leaf01294_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01294=true := by decide +kernel
#print axioms leaf01294_rectangular
def affine01294 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01294 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01294_transform : affine01294=(NestedInteger.clearedAll 3 raw01294 (IntegerComputedClassCell.leftNumerator ![(19/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01294_transform
theorem leaf01294_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01294=true := by decide +kernel
#print axioms leaf01294_sign
theorem leaf01294_log : RationalLog.accepts (1114301411/1073741824) (79624595/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01294_log
def leaf01294 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1618396691/1000000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(15/16)] ![(1/128),1,(1/16)] affine01294
theorem leaf01294_checked : FastNestedCellData.accepts 1 2 4 leaf01294=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1618396691/1000000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,(15/16)] ![(1/128),1,(1/16)] 1865884348038462401901756416000000000000 1939500182401509464632892088192161808384 1198408395906383785749406285824000000000000 raw01294 affine01294
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01294_raw leaf01294_rectangular
    leaf01294_transform leaf01294_sign leaf01294_log
#print axioms leaf01294_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
