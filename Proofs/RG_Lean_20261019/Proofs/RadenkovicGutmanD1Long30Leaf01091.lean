/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01091 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4724277809255617481020303998976000000000000 5338300500190174459723792218838438697238528 20844299825602332273702441320448000000000000))
theorem leaf01091_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4724277809255617481020303998976000000000000 5338300500190174459723792218838438697238528 20844299825602332273702441320448000000000000 raw01091=true := by decide +kernel
#print axioms leaf01091_raw
theorem leaf01091_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01091=true := by decide +kernel
#print axioms leaf01091_rectangular
def affine01091 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01091 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/16)] ![(3/80),1,(1/16)]))
theorem leaf01091_transform : affine01091=(NestedInteger.clearedAll 3 raw01091 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/16)] ![(3/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01091_transform
theorem leaf01091_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01091=true := by decide +kernel
#print axioms leaf01091_sign
theorem leaf01091_log : RationalLog.accepts (3863687433/4294967296) (-227250879/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01091_log
def leaf01091 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (256103613211/1000000000000) (3863687433/4294967296) (-227250879/4294967296) 1 8 ![60,0,4] ![(37/80),0,(1/16)] ![(3/80),1,(1/16)] affine01091
theorem leaf01091_checked : FastNestedCellData.accepts 1 2 4 leaf01091=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (256103613211/1000000000000) (3863687433/4294967296) (-227250879/4294967296) 1 8 ![60,0,4] ![(37/80),0,(1/16)] ![(3/80),1,(1/16)] 4724277809255617481020303998976000000000000 5338300500190174459723792218838438697238528 20844299825602332273702441320448000000000000 raw01091 affine01091
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01091_raw leaf01091_rectangular
    leaf01091_transform leaf01091_sign leaf01091_log
#print axioms leaf01091_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
