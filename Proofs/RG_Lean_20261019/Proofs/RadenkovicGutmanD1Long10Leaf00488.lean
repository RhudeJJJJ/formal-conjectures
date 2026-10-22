/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00488 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1198549175585030151440695296000000000000 1203738984969140777471951742578404098048 18526619883104935957978790494208000000000000))
theorem leaf00488_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1198549175585030151440695296000000000000 1203738984969140777471951742578404098048 18526619883104935957978790494208000000000000 raw00488=true := by decide +kernel
#print axioms leaf00488_raw
theorem leaf00488_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00488=true := by decide +kernel
#print axioms leaf00488_rectangular
def affine00488 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00488 (IntegerComputedClassCell.leftNumerator ![(3/64),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/64),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(3/64),0,0] ![(1/128),1,1]))
theorem leaf00488_transform : affine00488=(NestedInteger.clearedAll 3 raw00488 (IntegerComputedClassCell.leftNumerator ![(3/64),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/64),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(3/64),0,0] ![(1/128),1,1])) := by decide +kernel
#print axioms leaf00488_transform
theorem leaf00488_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00488=true := by decide +kernel
#print axioms leaf00488_sign
theorem leaf00488_log : RationalLog.accepts (4313284583/4294967296) (285599/134217728) 0 8=true := by decide +kernel
#print axioms leaf00488_log
def leaf00488 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (64973481/1000000000000) (4313284583/4294967296) (285599/134217728) 0 8 ![52,0,4] ![(3/64),0,0] ![(1/128),1,1] affine00488
theorem leaf00488_checked : FastNestedCellData.accepts 1 0 4 leaf00488=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (64973481/1000000000000) (4313284583/4294967296) (285599/134217728) 0 8 ![52,0,4] ![(3/64),0,0] ![(1/128),1,1] 1198549175585030151440695296000000000000 1203738984969140777471951742578404098048 18526619883104935957978790494208000000000000 raw00488 affine00488
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00488_raw leaf00488_rectangular
    leaf00488_transform leaf00488_sign leaf00488_log
#print axioms leaf00488_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
