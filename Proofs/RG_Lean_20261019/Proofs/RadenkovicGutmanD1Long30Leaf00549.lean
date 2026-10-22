/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00549 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11079584767351685833451110400000000 9678543176377208581015504674619392 161141065057850095311834316800000000))
theorem leaf00549_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11079584767351685833451110400000000 9678543176377208581015504674619392 161141065057850095311834316800000000 raw00549=true := by decide +kernel
#print axioms leaf00549_raw
theorem leaf00549_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00549=true := by decide +kernel
#print axioms leaf00549_rectangular
def affine00549 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00549 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00549_transform : affine00549=(NestedInteger.clearedAll 3 raw00549 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00549_transform
theorem leaf00549_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00549=true := by decide +kernel
#print axioms leaf00549_sign
theorem leaf00549_log : RationalLog.accepts (221204977/268435456) (-415582635/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00549_log
def leaf00549 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (96100079/1600000000) (221204977/268435456) (-415582635/4294967296) 1 8 ![60,0,4] ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)] affine00549
theorem leaf00549_checked : FastNestedCellData.accepts 1 2 4 leaf00549=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (96100079/1600000000) (221204977/268435456) (-415582635/4294967296) 1 8 ![60,0,4] ![(13/800),0,(1/2)] ![(1/3200),1,(1/2)] 11079584767351685833451110400000000 9678543176377208581015504674619392 161141065057850095311834316800000000 raw00549 affine00549
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00549_raw leaf00549_rectangular
    leaf00549_transform leaf00549_sign leaf00549_log
#print axioms leaf00549_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
