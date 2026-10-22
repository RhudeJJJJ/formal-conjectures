/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01183 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 535784365993341982198464512000000000000 650726808302882760685513322942259265536 21879048344081564761117949952000000000000))
theorem leaf01183_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 535784365993341982198464512000000000000 650726808302882760685513322942259265536 21879048344081564761117949952000000000000 raw01183=true := by decide +kernel
#print axioms leaf01183_raw
theorem leaf01183_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01183=true := by decide +kernel
#print axioms leaf01183_rectangular
def affine01183 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01183 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/32),0,(7/8)] ![(1/32),1,(1/16)]))
theorem leaf01183_transform : affine01183=(NestedInteger.clearedAll 3 raw01183 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(7/8)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(15/32),0,(7/8)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01183_transform
theorem leaf01183_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01183=true := by decide +kernel
#print axioms leaf01183_sign
theorem leaf01183_log : RationalLog.accepts (1266426829/1073741824) (354441821/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01183_log
def leaf01183 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (3717750871/125000000000) (1266426829/1073741824) (354441821/4294967296) 0 8 ![60,0,4] ![(15/32),0,(7/8)] ![(1/32),1,(1/16)] affine01183
theorem leaf01183_checked : FastNestedCellData.accepts 1 2 4 leaf01183=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (3717750871/125000000000) (1266426829/1073741824) (354441821/4294967296) 0 8 ![60,0,4] ![(15/32),0,(7/8)] ![(1/32),1,(1/16)] 535784365993341982198464512000000000000 650726808302882760685513322942259265536 21879048344081564761117949952000000000000 raw01183 affine01183
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01183_raw leaf01183_rectangular
    leaf01183_transform leaf01183_sign leaf01183_log
#print axioms leaf01183_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
