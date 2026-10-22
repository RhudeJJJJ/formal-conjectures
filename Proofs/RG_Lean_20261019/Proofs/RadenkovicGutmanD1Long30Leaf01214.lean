/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01214 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 242374213600382129291606884352000000000000 276914977916173580936817874980406667771904 21075590723602177639028550008832000000000000))
theorem leaf01214_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 242374213600382129291606884352000000000000 276914977916173580936817874980406667771904 21075590723602177639028550008832000000000000 raw01214=true := by decide +kernel
#print axioms leaf01214_raw
theorem leaf01214_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01214=true := by decide +kernel
#print axioms leaf01214_rectangular
def affine01214 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01214 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/64),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01214_transform : affine01214=(NestedInteger.clearedAll 3 raw01214 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/64),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01214_transform
theorem leaf01214_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01214=true := by decide +kernel
#print axioms leaf01214_sign
theorem leaf01214_log : RationalLog.accepts (4843405211/4294967296) (258071889/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01214_log
def leaf01214 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (13139132447/1000000000000) (4843405211/4294967296) (258071889/4294967296) 0 8 ![60,0,4] ![(21/64),0,(15/16)] ![(1/64),1,(1/16)] affine01214
theorem leaf01214_checked : FastNestedCellData.accepts 1 2 4 leaf01214=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (13139132447/1000000000000) (4843405211/4294967296) (258071889/4294967296) 0 8 ![60,0,4] ![(21/64),0,(15/16)] ![(1/64),1,(1/16)] 242374213600382129291606884352000000000000 276914977916173580936817874980406667771904 21075590723602177639028550008832000000000000 raw01214 affine01214
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01214_raw leaf01214_rectangular
    leaf01214_transform leaf01214_sign leaf01214_log
#print axioms leaf01214_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
