/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01017 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9680430488678368073446101876736000000000000 6406637938449192952852386114745500396683264 12208301124801042784259233808384000000000000))
theorem leaf01017_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9680430488678368073446101876736000000000000 6406637938449192952852386114745500396683264 12208301124801042784259233808384000000000000 raw01017=true := by decide +kernel
#print axioms leaf01017_raw
theorem leaf01017_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01017=true := by decide +kernel
#print axioms leaf01017_rectangular
def affine01017 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01017 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/8)] ![(1/80),1,(1/8)]))
theorem leaf01017_transform : affine01017=(NestedInteger.clearedAll 3 raw01017 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/8)] ![(1/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/8)] ![(1/80),1,(1/8)])) := by decide +kernel
#print axioms leaf01017_transform
theorem leaf01017_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01017=true := by decide +kernel
#print axioms leaf01017_sign
theorem leaf01017_log : RationalLog.accepts (1864184899/4294967296) (-448083237/1073741824) 2 8=true := by decide +kernel
#print axioms leaf01017_log
def leaf01017 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (524777188321/1000000000000) (1864184899/4294967296) (-448083237/1073741824) 2 8 ![60,0,4] ![(7/40),0,(1/8)] ![(1/80),1,(1/8)] affine01017
theorem leaf01017_checked : FastNestedCellData.accepts 1 2 4 leaf01017=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (524777188321/1000000000000) (1864184899/4294967296) (-448083237/1073741824) 2 8 ![60,0,4] ![(7/40),0,(1/8)] ![(1/80),1,(1/8)] 9680430488678368073446101876736000000000000 6406637938449192952852386114745500396683264 12208301124801042784259233808384000000000000 raw01017 affine01017
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01017_raw leaf01017_rectangular
    leaf01017_transform leaf01017_sign leaf01017_log
#print axioms leaf01017_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
