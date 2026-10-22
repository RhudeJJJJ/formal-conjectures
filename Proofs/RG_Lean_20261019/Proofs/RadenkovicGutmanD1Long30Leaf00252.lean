/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00252 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1537762326594388681955903275008000000000000 1270780990761346472220248452269921231962112 15244079858702892923298328346624000000000000))
theorem leaf00252_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1537762326594388681955903275008000000000000 1270780990761346472220248452269921231962112 15244079858702892923298328346624000000000000 raw00252=true := by decide +kernel
#print axioms leaf00252_raw
theorem leaf00252_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00252=true := by decide +kernel
#print axioms leaf00252_rectangular
def affine00252 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00252 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00252_transform : affine00252=(NestedInteger.clearedAll 3 raw00252 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00252_transform
theorem leaf00252_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00252=true := by decide +kernel
#print axioms leaf00252_sign
theorem leaf00252_log : RationalLog.accepts (3276179213/4294967296) (-581465747/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00252_log
def leaf00252 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (83362262763/1000000000000) (3276179213/4294967296) (-581465747/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00252
theorem leaf00252_checked : FastNestedCellData.accepts 1 2 4 leaf00252=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (83362262763/1000000000000) (3276179213/4294967296) (-581465747/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/8)] ![(1/6400),1,(1/8)] 1537762326594388681955903275008000000000000 1270780990761346472220248452269921231962112 15244079858702892923298328346624000000000000 raw00252 affine00252
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00252_raw leaf00252_rectangular
    leaf00252_transform leaf00252_sign leaf00252_log
#print axioms leaf00252_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
