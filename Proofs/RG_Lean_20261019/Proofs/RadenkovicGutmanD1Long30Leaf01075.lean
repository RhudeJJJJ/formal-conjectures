/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01075 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 382459730332761319255270490112000000000000 400437576868793222982515648131026225463296 1207115565403467857566009131008000000000000))
theorem leaf01075_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 382459730332761319255270490112000000000000 400437576868793222982515648131026225463296 1207115565403467857566009131008000000000000 raw01075=true := by decide +kernel
#print axioms leaf01075_raw
theorem leaf01075_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01075=true := by decide +kernel
#print axioms leaf01075_rectangular
def affine01075 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01075 (IntegerComputedClassCell.leftNumerator ![(59/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/160),0,0] ![(3/160),1,(1/16)]))
theorem leaf01075_transform : affine01075=(NestedInteger.clearedAll 3 raw01075 (IntegerComputedClassCell.leftNumerator ![(59/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/160),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01075_transform
theorem leaf01075_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01075=true := by decide +kernel
#print axioms leaf01075_sign
theorem leaf01075_log : RationalLog.accepts (3376700039/4294967296) (-258283275/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01075_log
def leaf01075 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (82932734103/250000000000) (3376700039/4294967296) (-258283275/2147483648) 1 8 ![60,0,4] ![(59/160),0,0] ![(3/160),1,(1/16)] affine01075
theorem leaf01075_checked : FastNestedCellData.accepts 1 2 4 leaf01075=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (82932734103/250000000000) (3376700039/4294967296) (-258283275/2147483648) 1 8 ![60,0,4] ![(59/160),0,0] ![(3/160),1,(1/16)] 382459730332761319255270490112000000000000 400437576868793222982515648131026225463296 1207115565403467857566009131008000000000000 raw01075 affine01075
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01075_raw leaf01075_rectangular
    leaf01075_transform leaf01075_sign leaf01075_log
#print axioms leaf01075_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
