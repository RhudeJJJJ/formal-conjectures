/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01069 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1100302290445695915134228732313600000000000 1076446965861619843102537864307917656686592 3609361147494671898698584162304000000000000))
theorem leaf01069_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1100302290445695915134228732313600000000000 1076446965861619843102537864307917656686592 3609361147494671898698584162304000000000000 raw01069=true := by decide +kernel
#print axioms leaf01069_raw
theorem leaf01069_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01069=true := by decide +kernel
#print axioms leaf01069_rectangular
def affine01069 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01069 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01069_transform : affine01069=(NestedInteger.clearedAll 3 raw01069 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01069_transform
theorem leaf01069_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01069=true := by decide +kernel
#print axioms leaf01069_sign
theorem leaf01069_log : RationalLog.accepts (3236579815/4294967296) (-1186681/8388608) 1 8=true := by decide +kernel
#print axioms leaf01069_log
def leaf01069 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (298237533423/1000000000000) (3236579815/4294967296) (-1186681/8388608) 1 8 ![60,0,4] ![(53/160),0,(1/2)] ![(3/160),1,(1/2)] affine01069
theorem leaf01069_checked : FastNestedCellData.accepts 1 2 4 leaf01069=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (298237533423/1000000000000) (3236579815/4294967296) (-1186681/8388608) 1 8 ![60,0,4] ![(53/160),0,(1/2)] ![(3/160),1,(1/2)] 1100302290445695915134228732313600000000000 1076446965861619843102537864307917656686592 3609361147494671898698584162304000000000000 raw01069 affine01069
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01069_raw leaf01069_rectangular
    leaf01069_transform leaf01069_sign leaf01069_log
#print axioms leaf01069_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
