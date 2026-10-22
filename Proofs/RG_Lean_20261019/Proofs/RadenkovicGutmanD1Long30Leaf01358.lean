/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01358 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 313006198117111042775449600000000000 313044346300401289633713259391483904 922449615161394881081892667392000000000000))
theorem leaf01358_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 313006198117111042775449600000000000 313044346300401289633713259391483904 922449615161394881081892667392000000000000 raw01358=true := by decide +kernel
#print axioms leaf01358_raw
theorem leaf01358_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01358=true := by decide +kernel
#print axioms leaf01358_rectangular
def affine01358 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01358 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/512),1,1]))
theorem leaf01358_transform : affine01358=(NestedInteger.clearedAll 3 raw01358 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01358_transform
theorem leaf01358_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01358=true := by decide +kernel
#print axioms leaf01358_sign
theorem leaf01358_log : RationalLog.accepts (4295489295/4294967296) (260983/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01358_log
def leaf01358 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (169681/500000000000) (4295489295/4294967296) (260983/4294967296) 0 8 ![60,0,4] ![(1/128),0,0] ![(1/512),1,1] affine01358
theorem leaf01358_checked : FastNestedCellData.accepts 1 2 4 leaf01358=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (169681/500000000000) (4295489295/4294967296) (260983/4294967296) 0 8 ![60,0,4] ![(1/128),0,0] ![(1/512),1,1] 313006198117111042775449600000000000 313044346300401289633713259391483904 922449615161394881081892667392000000000000 raw01358 affine01358
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01358_raw leaf01358_rectangular
    leaf01358_transform leaf01358_sign leaf01358_log
#print axioms leaf01358_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
