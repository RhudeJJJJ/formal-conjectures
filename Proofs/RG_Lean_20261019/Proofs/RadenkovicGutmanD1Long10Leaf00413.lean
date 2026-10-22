/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00413 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1271910726962168179827465519104000000000000 1700408323550661501638327967247151036104704 24661319776948104518525849174016000000000000))
theorem leaf00413_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1271910726962168179827465519104000000000000 1700408323550661501638327967247151036104704 24661319776948104518525849174016000000000000 raw00413=true := by decide +kernel
#print axioms leaf00413_raw
theorem leaf00413_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00413=true := by decide +kernel
#print axioms leaf00413_rectangular
def affine00413 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00413 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/8),1,(1/4)]))
theorem leaf00413_transform : affine00413=(NestedInteger.clearedAll 3 raw00413 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00413_transform
theorem leaf00413_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00413=true := by decide +kernel
#print axioms leaf00413_sign
theorem leaf00413_log : RationalLog.accepts (5371540959/4294967296) (120082391/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00413_log
def leaf00413 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (68950418669/1000000000000) (5371540959/4294967296) (120082391/1073741824) 0 8 ![52,0,4] ![(5/8),0,(3/4)] ![(1/8),1,(1/4)] affine00413
theorem leaf00413_checked : FastNestedCellData.accepts 1 0 4 leaf00413=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (68950418669/1000000000000) (5371540959/4294967296) (120082391/1073741824) 0 8 ![52,0,4] ![(5/8),0,(3/4)] ![(1/8),1,(1/4)] 1271910726962168179827465519104000000000000 1700408323550661501638327967247151036104704 24661319776948104518525849174016000000000000 raw00413 affine00413
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00413_raw leaf00413_rectangular
    leaf00413_transform leaf00413_sign leaf00413_log
#print axioms leaf00413_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
