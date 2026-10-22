/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01286 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1185604523419441874075648000000000 1236921333091421650386499286335488 663626861907030077104717824000000000))
theorem leaf01286_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1185604523419441874075648000000000 1236921333091421650386499286335488 663626861907030077104717824000000000 raw01286=true := by decide +kernel
#print axioms leaf01286_raw
theorem leaf01286_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01286=true := by decide +kernel
#print axioms leaf01286_rectangular
def affine01286 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01286 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01286_transform : affine01286=(NestedInteger.clearedAll 3 raw01286 (IntegerComputedClassCell.leftNumerator ![(5/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/32),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01286_transform
theorem leaf01286_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01286=true := by decide +kernel
#print axioms leaf01286_sign
theorem leaf01286_log : RationalLog.accepts (1118132787/1073741824) (21748941/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01286_log
def leaf01286 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (7455523/4000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(1/2)] ![(1/128),1,(1/4)] affine01286
theorem leaf01286_checked : FastNestedCellData.accepts 1 2 4 leaf01286=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (7455523/4000000000) (1118132787/1073741824) (21748941/1073741824) 0 8 ![60,0,4] ![(5/32),0,(1/2)] ![(1/128),1,(1/4)] 1185604523419441874075648000000000 1236921333091421650386499286335488 663626861907030077104717824000000000 raw01286 affine01286
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01286_raw leaf01286_rectangular
    leaf01286_transform leaf01286_sign leaf01286_log
#print axioms leaf01286_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
