/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01206 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 270018004989668164320620445696000000000000 310906947192438100157963618689768249884672 21240142433526555767064978522112000000000000))
theorem leaf01206_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 270018004989668164320620445696000000000000 310906947192438100157963618689768249884672 21240142433526555767064978522112000000000000 raw01206=true := by decide +kernel
#print axioms leaf01206_raw
theorem leaf01206_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01206=true := by decide +kernel
#print axioms leaf01206_rectangular
def affine01206 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01206 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/32),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01206_transform : affine01206=(NestedInteger.clearedAll 3 raw01206 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/32),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01206_transform
theorem leaf01206_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01206=true := by decide +kernel
#print axioms leaf01206_sign
theorem leaf01206_log : RationalLog.accepts (4874011687/4294967296) (8487487/134217728) 0 8=true := by decide +kernel
#print axioms leaf01206_log
def leaf01206 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (14637705381/1000000000000) (4874011687/4294967296) (8487487/134217728) 0 8 ![60,0,4] ![(11/32),0,(1/2)] ![(1/64),1,(1/4)] affine01206
theorem leaf01206_checked : FastNestedCellData.accepts 1 2 4 leaf01206=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (14637705381/1000000000000) (4874011687/4294967296) (8487487/134217728) 0 8 ![60,0,4] ![(11/32),0,(1/2)] ![(1/64),1,(1/4)] 270018004989668164320620445696000000000000 310906947192438100157963618689768249884672 21240142433526555767064978522112000000000000 raw01206 affine01206
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01206_raw leaf01206_rectangular
    leaf01206_transform leaf01206_sign leaf01206_log
#print axioms leaf01206_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
