/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01145 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 7158575821144895933353295872000000000000 9166681364973855774873730893271445536768 92271007666254559938435088384000000000000))
theorem leaf01145_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 7158575821144895933353295872000000000000 9166681364973855774873730893271445536768 92271007666254559938435088384000000000000 raw01145=true := by decide +kernel
#print axioms leaf01145_raw
theorem leaf01145_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01145=true := by decide +kernel
#print axioms leaf01145_rectangular
def affine01145 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01145 (IntegerComputedClassCell.leftNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf01145_transform : affine01145=(NestedInteger.clearedAll 3 raw01145 (IntegerComputedClassCell.leftNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01145_transform
theorem leaf01145_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01145=true := by decide +kernel
#print axioms leaf01145_sign
theorem leaf01145_log : RationalLog.accepts (1250694653/1073741824) (327597641/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01145_log
def leaf01145 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (24836299063/250000000000) (1250694653/1073741824) (327597641/4294967296) 0 8 ![60,0,4] ![(15/16),0,0] ![(1/16),1,(1/2)] affine01145
theorem leaf01145_checked : FastNestedCellData.accepts 1 2 4 leaf01145=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (24836299063/250000000000) (1250694653/1073741824) (327597641/4294967296) 0 8 ![60,0,4] ![(15/16),0,0] ![(1/16),1,(1/2)] 7158575821144895933353295872000000000000 9166681364973855774873730893271445536768 92271007666254559938435088384000000000000 raw01145 affine01145
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01145_raw leaf01145_rectangular
    leaf01145_transform leaf01145_sign leaf01145_log
#print axioms leaf01145_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
