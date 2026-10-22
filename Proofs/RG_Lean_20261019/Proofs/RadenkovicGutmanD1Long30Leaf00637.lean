/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00637 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 23142936230236243101963255808000000000000 11861926645589155331962835957630518689792 36933165534061467479272587264000000000000))
theorem leaf00637_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 23142936230236243101963255808000000000000 11861926645589155331962835957630518689792 36933165534061467479272587264000000000000 raw00637=true := by decide +kernel
#print axioms leaf00637_raw
theorem leaf00637_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00637=true := by decide +kernel
#print axioms leaf00637_rectangular
def affine00637 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00637 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00637_transform : affine00637=(NestedInteger.clearedAll 3 raw00637 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00637_transform
theorem leaf00637_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00637=true := by decide +kernel
#print axioms leaf00637_sign
theorem leaf00637_log : RationalLog.accepts (104139873/268435456) (-2033399873/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00637_log
def leaf00637 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (321172758253/1000000000000) (104139873/268435456) (-2033399873/4294967296) 2 8 ![60,0,4] ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)] affine00637
theorem leaf00637_checked : FastNestedCellData.accepts 1 2 4 leaf00637=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (321172758253/1000000000000) (104139873/268435456) (-2033399873/4294967296) 2 8 ![60,0,4] ![(73/3200),0,(1/8)] ![(3/6400),1,(1/8)] 23142936230236243101963255808000000000000 11861926645589155331962835957630518689792 36933165534061467479272587264000000000000 raw00637 affine00637
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00637_raw leaf00637_rectangular
    leaf00637_transform leaf00637_sign leaf00637_log
#print axioms leaf00637_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
