/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00161 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1278094564525074039274523852800000000000 993312880827033324791003151646171594752 8960305543072339991302923878400000000000))
theorem leaf00161_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1278094564525074039274523852800000000000 993312880827033324791003151646171594752 8960305543072339991302923878400000000000 raw00161=true := by decide +kernel
#print axioms leaf00161_raw
theorem leaf00161_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00161=true := by decide +kernel
#print axioms leaf00161_rectangular
def affine00161 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00161 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00161_transform : affine00161=(NestedInteger.clearedAll 3 raw00161 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00161_transform
theorem leaf00161_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00161=true := by decide +kernel
#print axioms leaf00161_sign
theorem leaf00161_log : RationalLog.accepts (3004863663/4294967296) (-767106415/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00161_log
def leaf00161 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2771425807/25000000000) (3004863663/4294967296) (-767106415/4294967296) 1 8 ![60,0,4] ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)] affine00161
theorem leaf00161_checked : FastNestedCellData.accepts 1 2 4 leaf00161=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2771425807/25000000000) (3004863663/4294967296) (-767106415/4294967296) 1 8 ![60,0,4] ![(7/2000),0,(1/16)] ![(3/32000),1,(1/16)] 1278094564525074039274523852800000000000 993312880827033324791003151646171594752 8960305543072339991302923878400000000000 raw00161 affine00161
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00161_raw leaf00161_rectangular
    leaf00161_transform leaf00161_sign leaf00161_log
#print axioms leaf00161_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
