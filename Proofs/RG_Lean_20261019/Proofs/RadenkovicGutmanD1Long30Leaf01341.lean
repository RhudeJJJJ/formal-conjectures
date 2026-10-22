/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01341 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1261038909252212804183654400000000000 1269480662969902040780649099662721024 11606394896161201071083592089600000000000))
theorem leaf01341_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1261038909252212804183654400000000000 1269480662969902040780649099662721024 11606394896161201071083592089600000000000 raw01341=true := by decide +kernel
#print axioms leaf01341_raw
theorem leaf01341_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01341=true := by decide +kernel
#print axioms leaf01341_rectangular
def affine01341 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01341 (IntegerComputedClassCell.leftNumerator ![(15/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(15/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(15/256),0,0] ![(1/256),1,1]))
theorem leaf01341_transform : affine01341=(NestedInteger.clearedAll 3 raw01341 (IntegerComputedClassCell.leftNumerator ![(15/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(15/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(15/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01341_transform
theorem leaf01341_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01341=true := by decide +kernel
#print axioms leaf01341_sign
theorem leaf01341_log : RationalLog.accepts (1080811541/1073741824) (440409/134217728) 0 8=true := by decide +kernel
#print axioms leaf01341_log
def leaf01341 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (10937769/100000000000) (1080811541/1073741824) (440409/134217728) 0 8 ![60,0,4] ![(15/256),0,0] ![(1/256),1,1] affine01341
theorem leaf01341_checked : FastNestedCellData.accepts 1 2 4 leaf01341=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (10937769/100000000000) (1080811541/1073741824) (440409/134217728) 0 8 ![60,0,4] ![(15/256),0,0] ![(1/256),1,1] 1261038909252212804183654400000000000 1269480662969902040780649099662721024 11606394896161201071083592089600000000000 raw01341 affine01341
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01341_raw leaf01341_rectangular
    leaf01341_transform leaf01341_sign leaf01341_log
#print axioms leaf01341_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
