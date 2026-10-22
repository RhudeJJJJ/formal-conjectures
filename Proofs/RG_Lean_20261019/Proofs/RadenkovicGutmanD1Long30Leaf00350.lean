/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00350 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2826721710784964260068616830976000000000000 6187225167788157158161602496067574693888 10094216098558600123936407552000000000000))
theorem leaf00350_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2826721710784964260068616830976000000000000 6187225167788157158161602496067574693888 10094216098558600123936407552000000000000 raw00350=true := by decide +kernel
#print axioms leaf00350_raw
theorem leaf00350_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00350=true := by decide +kernel
#print axioms leaf00350_rectangular
def affine00350 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00350 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00350_transform : affine00350=(NestedInteger.clearedAll 3 raw00350 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00350_transform
theorem leaf00350_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00350=true := by decide +kernel
#print axioms leaf00350_sign
theorem leaf00350_log : RationalLog.accepts (2914221/2147483648) (-14178652677/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00350_log
def leaf00350 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (612947563969/1000000000000) (2914221/2147483648) (-14178652677/4294967296) 10 8 ![60,0,4] ![(27/3200),0,0] ![(1/6400),1,(1/16)] affine00350
theorem leaf00350_checked : FastNestedCellData.accepts 1 2 4 leaf00350=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (612947563969/1000000000000) (2914221/2147483648) (-14178652677/4294967296) 10 8 ![60,0,4] ![(27/3200),0,0] ![(1/6400),1,(1/16)] 2826721710784964260068616830976000000000000 6187225167788157158161602496067574693888 10094216098558600123936407552000000000000 raw00350 affine00350
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00350_raw leaf00350_rectangular
    leaf00350_transform leaf00350_sign leaf00350_log
#print axioms leaf00350_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
