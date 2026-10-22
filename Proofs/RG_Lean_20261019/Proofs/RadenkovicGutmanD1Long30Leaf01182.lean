/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01182 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 85726485897852832363367628800000000000 104117635565535019244658035932394422272 3500652680297565787084396953600000000000))
theorem leaf01182_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 85726485897852832363367628800000000000 104117635565535019244658035932394422272 3500652680297565787084396953600000000000 raw01182=true := by decide +kernel
#print axioms leaf01182_raw
theorem leaf01182_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01182=true := by decide +kernel
#print axioms leaf01182_rectangular
def affine01182 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01182 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/32),0,(3/4)] ![(1/32),1,(1/8)]))
theorem leaf01182_transform : affine01182=(NestedInteger.clearedAll 3 raw01182 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(3/4)] ![(1/32),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/32),0,(3/4)] ![(1/32),1,(1/8)])) := by decide +kernel
#print axioms leaf01182_transform
theorem leaf01182_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01182=true := by decide +kernel
#print axioms leaf01182_sign
theorem leaf01182_log : RationalLog.accepts (5065712787/4294967296) (88611035/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01182_log
def leaf01182 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (371779369/12500000000) (5065712787/4294967296) (88611035/1073741824) 0 8 ![60,0,4] ![(15/32),0,(3/4)] ![(1/32),1,(1/8)] affine01182
theorem leaf01182_checked : FastNestedCellData.accepts 1 2 4 leaf01182=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (371779369/12500000000) (5065712787/4294967296) (88611035/1073741824) 0 8 ![60,0,4] ![(15/32),0,(3/4)] ![(1/32),1,(1/8)] 85726485897852832363367628800000000000 104117635565535019244658035932394422272 3500652680297565787084396953600000000000 raw01182 affine01182
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01182_raw leaf01182_rectangular
    leaf01182_transform leaf01182_sign leaf01182_log
#print axioms leaf01182_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
