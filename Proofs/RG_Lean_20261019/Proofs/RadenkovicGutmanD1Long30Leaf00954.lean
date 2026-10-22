/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00954 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1294643627702901132253724672000000000 854649834710042223347187777489862656 3044371909802547805465608192000000000))
theorem leaf00954_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1294643627702901132253724672000000000 854649834710042223347187777489862656 3044371909802547805465608192000000000 raw00954=true := by decide +kernel
#print axioms leaf00954_raw
theorem leaf00954_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00954=true := by decide +kernel
#print axioms leaf00954_rectangular
def affine00954 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00954 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00954_transform : affine00954=(NestedInteger.clearedAll 3 raw00954 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00954_transform
theorem leaf00954_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00954=true := by decide +kernel
#print axioms leaf00954_sign
theorem leaf00954_log : RationalLog.accepts (276725957/536870912) (-1423201845/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00954_log
def leaf00954 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1122924347/4000000000) (276725957/536870912) (-1423201845/4294967296) 1 8 ![60,0,4] ![(31/320),0,(1/2)] ![(1/320),1,(1/2)] affine00954
theorem leaf00954_checked : FastNestedCellData.accepts 1 2 4 leaf00954=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1122924347/4000000000) (276725957/536870912) (-1423201845/4294967296) 1 8 ![60,0,4] ![(31/320),0,(1/2)] ![(1/320),1,(1/2)] 1294643627702901132253724672000000000 854649834710042223347187777489862656 3044371909802547805465608192000000000 raw00954 affine00954
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00954_raw leaf00954_rectangular
    leaf00954_transform leaf00954_sign leaf00954_log
#print axioms leaf00954_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
