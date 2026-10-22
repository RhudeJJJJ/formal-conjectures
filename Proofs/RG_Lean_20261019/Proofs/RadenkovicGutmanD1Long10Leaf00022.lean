/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00022 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 123723413606970466485357510656000000000000 117743921525517962696245257211176378433536 5851740650900272552643429138432000000000000))
theorem leaf00022_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 123723413606970466485357510656000000000000 117743921525517962696245257211176378433536 5851740650900272552643429138432000000000000 raw00022=true := by decide +kernel
#print axioms leaf00022_raw
theorem leaf00022_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00022=true := by decide +kernel
#print axioms leaf00022_rectangular
def affine00022 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00022 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)]))
theorem leaf00022_transform : affine00022=(NestedInteger.clearedAll 3 raw00022 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00022_transform
theorem leaf00022_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00022=true := by decide +kernel
#print axioms leaf00022_sign
theorem leaf00022_log : RationalLog.accepts (4006772637/4294967296) (-74579819/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00022_log
def leaf00022 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (20121179073/1000000000000) (4006772637/4294967296) (-74579819/2147483648) 1 8 ![52,0,4] ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)] affine00022
theorem leaf00022_checked : FastNestedCellData.accepts 1 0 4 leaf00022=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (20121179073/1000000000000) (4006772637/4294967296) (-74579819/2147483648) 1 8 ![52,0,4] ![(41/16000),0,(1/4)] ![(3/16000),1,(1/4)] 123723413606970466485357510656000000000000 117743921525517962696245257211176378433536 5851740650900272552643429138432000000000000 raw00022 affine00022
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00022_raw leaf00022_rectangular
    leaf00022_transform leaf00022_sign leaf00022_log
#print axioms leaf00022_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
