/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00277 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 117134388529089512831537958092800000000000 94352504088395623426879859089554838388736 990598074279457778753997897728000000000000))
theorem leaf00277_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 117134388529089512831537958092800000000000 94352504088395623426879859089554838388736 990598074279457778753997897728000000000000 raw00277=true := by decide +kernel
#print axioms leaf00277_raw
theorem leaf00277_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00277=true := by decide +kernel
#print axioms leaf00277_rectangular
def affine00277 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00277 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00277_transform : affine00277=(NestedInteger.clearedAll 3 raw00277 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00277_transform
theorem leaf00277_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00277=true := by decide +kernel
#print axioms leaf00277_sign
theorem leaf00277_log : RationalLog.accepts (3158758335/4294967296) (-659846433/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00277_log
def leaf00277 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (95248018887/1000000000000) (3158758335/4294967296) (-659846433/4294967296) 1 8 ![60,0,4] ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00277
theorem leaf00277_checked : FastNestedCellData.accepts 1 2 4 leaf00277=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (95248018887/1000000000000) (3158758335/4294967296) (-659846433/4294967296) 1 8 ![60,0,4] ![(39/6400),0,(1/8)] ![(1/6400),1,(1/8)] 117134388529089512831537958092800000000000 94352504088395623426879859089554838388736 990598074279457778753997897728000000000000 raw00277 affine00277
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00277_raw leaf00277_rectangular
    leaf00277_transform leaf00277_sign leaf00277_log
#print axioms leaf00277_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
