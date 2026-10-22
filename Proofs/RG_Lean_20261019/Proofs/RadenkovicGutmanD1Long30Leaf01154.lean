/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01154 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1654310461035328875860649312256000000000000 2119129070652631187587649810664299832541184 23629803804191890226384652468224000000000000))
theorem leaf01154_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1654310461035328875860649312256000000000000 2119129070652631187587649810664299832541184 23629803804191890226384652468224000000000000 raw01154=true := by decide +kernel
#print axioms leaf01154_raw
theorem leaf01154_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01154=true := by decide +kernel
#print axioms leaf01154_rectangular
def affine01154 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01154 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]))
theorem leaf01154_transform : affine01154=(NestedInteger.clearedAll 3 raw01154 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/8),0,(15/16)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01154_transform
theorem leaf01154_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01154=true := by decide +kernel
#print axioms leaf01154_sign
theorem leaf01154_log : RationalLog.accepts (5048950759/4294967296) (347326511/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01154_log
def leaf01154 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (89680349791/1000000000000) (5048950759/4294967296) (347326511/4294967296) 0 8 ![60,0,4] ![(7/8),0,(15/16)] ![(1/16),1,(1/16)] affine01154
theorem leaf01154_checked : FastNestedCellData.accepts 1 2 4 leaf01154=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (89680349791/1000000000000) (5048950759/4294967296) (347326511/4294967296) 0 8 ![60,0,4] ![(7/8),0,(15/16)] ![(1/16),1,(1/16)] 1654310461035328875860649312256000000000000 2119129070652631187587649810664299832541184 23629803804191890226384652468224000000000000 raw01154 affine01154
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01154_raw leaf01154_rectangular
    leaf01154_transform leaf01154_sign leaf01154_log
#print axioms leaf01154_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
