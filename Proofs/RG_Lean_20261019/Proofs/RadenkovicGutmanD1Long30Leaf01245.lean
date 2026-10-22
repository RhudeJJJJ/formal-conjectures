/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01245 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 89152901435725837162707419136000000000000 96070947382680280648519050818006997270528 19878166057946774822446922989568000000000000))
theorem leaf01245_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 89152901435725837162707419136000000000000 96070947382680280648519050818006997270528 19878166057946774822446922989568000000000000 raw01245=true := by decide +kernel
#print axioms leaf01245_raw
theorem leaf01245_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01245=true := by decide +kernel
#print axioms leaf01245_rectangular
def affine01245 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01245 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(1/64),1,(1/2)]))
theorem leaf01245_transform : affine01245=(NestedInteger.clearedAll 3 raw01245 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01245_transform
theorem leaf01245_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01245=true := by decide +kernel
#print axioms leaf01245_sign
theorem leaf01245_log : RationalLog.accepts (4605985523/4294967296) (150136417/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01245_log
def leaf01245 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4832988471/1000000000000) (4605985523/4294967296) (150136417/4294967296) 0 8 ![60,0,4] ![(7/32),0,0] ![(1/64),1,(1/2)] affine01245
theorem leaf01245_checked : FastNestedCellData.accepts 1 2 4 leaf01245=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4832988471/1000000000000) (4605985523/4294967296) (150136417/4294967296) 0 8 ![60,0,4] ![(7/32),0,0] ![(1/64),1,(1/2)] 89152901435725837162707419136000000000000 96070947382680280648519050818006997270528 19878166057946774822446922989568000000000000 raw01245 affine01245
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01245_raw leaf01245_rectangular
    leaf01245_transform leaf01245_sign leaf01245_log
#print axioms leaf01245_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
