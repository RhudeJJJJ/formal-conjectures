/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01165 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1064937929623487152749478412288000000000000 1351254103787411614025637721444397271220224 23406283068468518965859862970368000000000000))
theorem leaf01165_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1064937929623487152749478412288000000000000 1351254103787411614025637721444397271220224 23406283068468518965859862970368000000000000 raw01165=true := by decide +kernel
#print axioms leaf01165_raw
theorem leaf01165_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01165=true := by decide +kernel
#print axioms leaf01165_rectangular
def affine01165 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01165 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/8),1,(1/2)]))
theorem leaf01165_transform : affine01165=(NestedInteger.clearedAll 3 raw01165 (IntegerComputedClassCell.leftNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,0] ![(1/8),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/8),0,0] ![(1/8),1,(1/2)])) := by decide +kernel
#print axioms leaf01165_transform
theorem leaf01165_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01165=true := by decide +kernel
#print axioms leaf01165_sign
theorem leaf01165_log : RationalLog.accepts (5152258031/4294967296) (6106609/67108864) 0 8=true := by decide +kernel
#print axioms leaf01165_log
def leaf01165 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (57730400843/1000000000000) (5152258031/4294967296) (6106609/67108864) 0 8 ![60,0,4] ![(5/8),0,0] ![(1/8),1,(1/2)] affine01165
theorem leaf01165_checked : FastNestedCellData.accepts 1 2 4 leaf01165=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (57730400843/1000000000000) (5152258031/4294967296) (6106609/67108864) 0 8 ![60,0,4] ![(5/8),0,0] ![(1/8),1,(1/2)] 1064937929623487152749478412288000000000000 1351254103787411614025637721444397271220224 23406283068468518965859862970368000000000000 raw01165 affine01165
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01165_raw leaf01165_rectangular
    leaf01165_transform leaf01165_sign leaf01165_log
#print axioms leaf01165_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
