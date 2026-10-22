/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00542 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1066126472669426519380066304000000000000 640924840701266388218986368876819775488 2707435700876479649506394112000000000000))
theorem leaf00542_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1066126472669426519380066304000000000000 640924840701266388218986368876819775488 2707435700876479649506394112000000000000 raw00542=true := by decide +kernel
#print axioms leaf00542_raw
theorem leaf00542_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00542=true := by decide +kernel
#print axioms leaf00542_rectangular
def affine00542 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00542 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00542_transform : affine00542=(NestedInteger.clearedAll 3 raw00542 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00542_transform
theorem leaf00542_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00542=true := by decide +kernel
#print axioms leaf00542_sign
theorem leaf00542_log : RationalLog.accepts (2087777313/4294967296) (-1549074361/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00542_log
def leaf00542 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3698869241/15625000000) (2087777313/4294967296) (-1549074361/4294967296) 2 8 ![60,0,4] ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00542
theorem leaf00542_checked : FastNestedCellData.accepts 1 2 4 leaf00542=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3698869241/15625000000) (2087777313/4294967296) (-1549074361/4294967296) 2 8 ![60,0,4] ![(51/3200),0,(1/8)] ![(1/3200),1,(1/8)] 1066126472669426519380066304000000000000 640924840701266388218986368876819775488 2707435700876479649506394112000000000000 raw00542 affine00542
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00542_raw leaf00542_rectangular
    leaf00542_transform leaf00542_sign leaf00542_log
#print axioms leaf00542_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
