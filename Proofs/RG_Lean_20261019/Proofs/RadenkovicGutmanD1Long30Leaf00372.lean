/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00372 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2575708629708852897930822025216000000000000 1888998661426297506990107291495200783859712 13528655555597396191565957824512000000000000))
theorem leaf00372_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2575708629708852897930822025216000000000000 1888998661426297506990107291495200783859712 13528655555597396191565957824512000000000000 raw00372=true := by decide +kernel
#print axioms leaf00372_raw
theorem leaf00372_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00372=true := by decide +kernel
#print axioms leaf00372_rectangular
def affine00372 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00372 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00372_transform : affine00372=(NestedInteger.clearedAll 3 raw00372 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00372_transform
theorem leaf00372_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00372=true := by decide +kernel
#print axioms leaf00372_sign
theorem leaf00372_log : RationalLog.accepts (2763955947/4294967296) (-59160623/268435456) 1 8=true := by decide +kernel
#print axioms leaf00372_log
def leaf00372 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (139629444601/1000000000000) (2763955947/4294967296) (-59160623/268435456) 1 8 ![60,0,4] ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00372
theorem leaf00372_checked : FastNestedCellData.accepts 1 2 4 leaf00372=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (139629444601/1000000000000) (2763955947/4294967296) (-59160623/268435456) 1 8 ![60,0,4] ![(29/3200),0,(1/8)] ![(1/6400),1,(1/8)] 2575708629708852897930822025216000000000000 1888998661426297506990107291495200783859712 13528655555597396191565957824512000000000000 raw00372 affine00372
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00372_raw leaf00372_rectangular
    leaf00372_transform leaf00372_sign leaf00372_log
#print axioms leaf00372_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
