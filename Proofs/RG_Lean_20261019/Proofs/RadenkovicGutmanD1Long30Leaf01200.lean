/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01200 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3736439331894219943478873292800000000000 4334805401483195563694647761027677028352 267510853073172808322743533568000000000000))
theorem leaf01200_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3736439331894219943478873292800000000000 4334805401483195563694647761027677028352 267510853073172808322743533568000000000000 raw01200=true := by decide +kernel
#print axioms leaf01200_raw
theorem leaf01200_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01200=true := by decide +kernel
#print axioms leaf01200_rectangular
def affine01200 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01200 (IntegerComputedClassCell.leftNumerator ![(23/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf01200_transform : affine01200=(NestedInteger.clearedAll 3 raw01200 (IntegerComputedClassCell.leftNumerator ![(23/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01200_transform
theorem leaf01200_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01200=true := by decide +kernel
#print axioms leaf01200_sign
theorem leaf01200_log : RationalLog.accepts (4903323385/4294967296) (71118901/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01200_log
def leaf01200 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4051055641/250000000000) (4903323385/4294967296) (71118901/1073741824) 0 8 ![60,0,4] ![(23/64),0,0] ![(1/64),1,(1/2)] affine01200
theorem leaf01200_checked : FastNestedCellData.accepts 1 2 4 leaf01200=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4051055641/250000000000) (4903323385/4294967296) (71118901/1073741824) 0 8 ![60,0,4] ![(23/64),0,0] ![(1/64),1,(1/2)] 3736439331894219943478873292800000000000 4334805401483195563694647761027677028352 267510853073172808322743533568000000000000 raw01200 affine01200
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01200_raw leaf01200_rectangular
    leaf01200_transform leaf01200_sign leaf01200_log
#print axioms leaf01200_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
