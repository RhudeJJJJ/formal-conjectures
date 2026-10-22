/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00395 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 61740873053955228908002476032000000000000 79968035385771481104321301286182063177728 373321849517930258522676658176000000000000))
theorem leaf00395_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 61740873053955228908002476032000000000000 79968035385771481104321301286182063177728 373321849517930258522676658176000000000000 raw00395=true := by decide +kernel
#print axioms leaf00395_raw
theorem leaf00395_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00395=true := by decide +kernel
#print axioms leaf00395_rectangular
def affine00395 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00395 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00395_transform : affine00395=(NestedInteger.clearedAll 3 raw00395 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/8),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00395_transform
theorem leaf00395_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00395=true := by decide +kernel
#print axioms leaf00395_sign
theorem leaf00395_log : RationalLog.accepts (2290766939/2147483648) (138705773/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00395_log
def leaf00395 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (53551670957/250000000000) (2290766939/2147483648) (138705773/4294967296) 0 8 ![52,0,4] ![(5/8),0,(3/4)] ![(1/16),1,(1/4)] affine00395
theorem leaf00395_checked : FastNestedCellData.accepts 1 0 4 leaf00395=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (53551670957/250000000000) (2290766939/2147483648) (138705773/4294967296) 0 8 ![52,0,4] ![(5/8),0,(3/4)] ![(1/16),1,(1/4)] 61740873053955228908002476032000000000000 79968035385771481104321301286182063177728 373321849517930258522676658176000000000000 raw00395 affine00395
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00395_raw leaf00395_rectangular
    leaf00395_transform leaf00395_sign leaf00395_log
#print axioms leaf00395_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
