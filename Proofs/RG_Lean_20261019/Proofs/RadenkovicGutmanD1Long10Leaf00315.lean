/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00315 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 32529996585089429630557670604800000000000 7217762579654486582940843554197035024384 10232418772579309609217635123200000000000))
theorem leaf00315_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 32529996585089429630557670604800000000000 7217762579654486582940843554197035024384 10232418772579309609217635123200000000000 raw00315=true := by decide +kernel
#print axioms leaf00315_raw
theorem leaf00315_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00315=true := by decide +kernel
#print axioms leaf00315_rectangular
def affine00315 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00315 (IntegerComputedClassCell.leftNumerator ![(31/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/320),0,0] ![(1/320),1,(1/4)]))
theorem leaf00315_transform : affine00315=(NestedInteger.clearedAll 3 raw00315 (IntegerComputedClassCell.leftNumerator ![(31/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/320),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00315_transform
theorem leaf00315_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00315=true := by decide +kernel
#print axioms leaf00315_sign
theorem leaf00315_log : RationalLog.accepts (279400257/2147483648) (-1094898147/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00315_log
def leaf00315 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (70538185937/100000000000) (279400257/2147483648) (-1094898147/1073741824) 3 8 ![52,0,4] ![(31/320),0,0] ![(1/320),1,(1/4)] affine00315
theorem leaf00315_checked : FastNestedCellData.accepts 1 0 4 leaf00315=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (70538185937/100000000000) (279400257/2147483648) (-1094898147/1073741824) 3 8 ![52,0,4] ![(31/320),0,0] ![(1/320),1,(1/4)] 32529996585089429630557670604800000000000 7217762579654486582940843554197035024384 10232418772579309609217635123200000000000 raw00315 affine00315
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00315_raw leaf00315_rectangular
    leaf00315_transform leaf00315_sign leaf00315_log
#print axioms leaf00315_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
