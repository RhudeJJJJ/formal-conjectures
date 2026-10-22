/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01163 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1316405682999202849735000981504000000000000 1684686593641155352771571657720215258529792 23607450832713195430097576787968000000000000))
theorem leaf01163_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1316405682999202849735000981504000000000000 1684686593641155352771571657720215258529792 23607450832713195430097576787968000000000000 raw01163=true := by decide +kernel
#print axioms leaf01163_raw
theorem leaf01163_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01163=true := by decide +kernel
#print axioms leaf01163_rectangular
def affine01163 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01163 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01163_transform : affine01163=(NestedInteger.clearedAll 3 raw01163 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/4),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01163_transform
theorem leaf01163_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01163=true := by decide +kernel
#print axioms leaf01163_sign
theorem leaf01163_log : RationalLog.accepts (5130418507/4294967296) (381700819/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01163_log
def leaf01163 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (71362495069/1000000000000) (5130418507/4294967296) (381700819/4294967296) 0 8 ![60,0,4] ![(3/4),0,(7/8)] ![(1/16),1,(1/16)] affine01163
theorem leaf01163_checked : FastNestedCellData.accepts 1 2 4 leaf01163=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (71362495069/1000000000000) (5130418507/4294967296) (381700819/4294967296) 0 8 ![60,0,4] ![(3/4),0,(7/8)] ![(1/16),1,(1/16)] 1316405682999202849735000981504000000000000 1684686593641155352771571657720215258529792 23607450832713195430097576787968000000000000 raw01163 affine01163
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01163_raw leaf01163_rectangular
    leaf01163_transform leaf01163_sign leaf01163_log
#print axioms leaf01163_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
