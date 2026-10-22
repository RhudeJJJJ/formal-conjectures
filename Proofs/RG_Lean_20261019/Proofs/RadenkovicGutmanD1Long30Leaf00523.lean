/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00523 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 512335818656945734601622421504000000000000 400609100582081141144963330655017341288448 3606000831353563257318825525248000000000000))
theorem leaf00523_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 512335818656945734601622421504000000000000 400609100582081141144963330655017341288448 3606000831353563257318825525248000000000000 raw00523=true := by decide +kernel
#print axioms leaf00523_raw
theorem leaf00523_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00523=true := by decide +kernel
#print axioms leaf00523_rectangular
def affine00523 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00523 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00523_transform : affine00523=(NestedInteger.clearedAll 3 raw00523 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00523_transform
theorem leaf00523_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00523=true := by decide +kernel
#print axioms leaf00523_sign
theorem leaf00523_log : RationalLog.accepts (3022558477/4294967296) (-188624391/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00523_log
def leaf00523 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (55547560763/500000000000) (3022558477/4294967296) (-188624391/1073741824) 1 8 ![60,0,4] ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00523
theorem leaf00523_checked : FastNestedCellData.accepts 1 2 4 leaf00523=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (55547560763/500000000000) (3022558477/4294967296) (-188624391/1073741824) 1 8 ![60,0,4] ![(47/3200),0,(1/4)] ![(1/3200),1,(1/4)] 512335818656945734601622421504000000000000 400609100582081141144963330655017341288448 3606000831353563257318825525248000000000000 raw00523 affine00523
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00523_raw leaf00523_rectangular
    leaf00523_transform leaf00523_sign leaf00523_log
#print axioms leaf00523_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
