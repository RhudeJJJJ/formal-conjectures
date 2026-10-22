/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01239 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1956254425558584660670283776000000000000 2144254649685826120060110150868683194368 315929930263303529165322452992000000000000))
theorem leaf01239_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1956254425558584660670283776000000000000 2144254649685826120060110150868683194368 315929930263303529165322452992000000000000 raw01239=true := by decide +kernel
#print axioms leaf01239_raw
theorem leaf01239_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01239=true := by decide +kernel
#print axioms leaf01239_rectangular
def affine01239 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01239 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/4),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01239_transform : affine01239=(NestedInteger.clearedAll 3 raw01239 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/4),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01239_transform
theorem leaf01239_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01239=true := by decide +kernel
#print axioms leaf01239_sign
theorem leaf01239_log : RationalLog.accepts (1168996583/1073741824) (182527905/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01239_log
def leaf01239 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3393560477/500000000000) (1168996583/1073741824) (182527905/4294967296) 0 8 ![60,0,4] ![(1/4),0,(15/16)] ![(1/64),1,(1/16)] affine01239
theorem leaf01239_checked : FastNestedCellData.accepts 1 2 4 leaf01239=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3393560477/500000000000) (1168996583/1073741824) (182527905/4294967296) 0 8 ![60,0,4] ![(1/4),0,(15/16)] ![(1/64),1,(1/16)] 1956254425558584660670283776000000000000 2144254649685826120060110150868683194368 315929930263303529165322452992000000000000 raw01239 affine01239
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01239_raw leaf01239_rectangular
    leaf01239_transform leaf01239_sign leaf01239_log
#print axioms leaf01239_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
