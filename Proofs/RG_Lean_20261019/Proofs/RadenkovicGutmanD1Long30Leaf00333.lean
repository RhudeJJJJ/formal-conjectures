/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00333 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 68960370487082398464079822848000000000000 60158333929053643676129206555038713905152 1005763692657621580076258689024000000000000))
theorem leaf00333_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 68960370487082398464079822848000000000000 60158333929053643676129206555038713905152 1005763692657621580076258689024000000000000 raw00333=true := by decide +kernel
#print axioms leaf00333_raw
theorem leaf00333_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00333=true := by decide +kernel
#print axioms leaf00333_rectangular
def affine00333 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00333 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00333_transform : affine00333=(NestedInteger.clearedAll 3 raw00333 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00333_transform
theorem leaf00333_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00333=true := by decide +kernel
#print axioms leaf00333_sign
theorem leaf00333_log : RationalLog.accepts (1767651299/2147483648) (-208998543/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00333_log
def leaf00333 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (29906793399/500000000000) (1767651299/2147483648) (-208998543/2147483648) 1 8 ![60,0,4] ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)] affine00333
theorem leaf00333_checked : FastNestedCellData.accepts 1 2 4 leaf00333=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (29906793399/500000000000) (1767651299/2147483648) (-208998543/2147483648) 1 8 ![60,0,4] ![(1/128),0,(1/4)] ![(1/6400),1,(1/4)] 68960370487082398464079822848000000000000 60158333929053643676129206555038713905152 1005763692657621580076258689024000000000000 raw00333 affine00333
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00333_raw leaf00333_rectangular
    leaf00333_transform leaf00333_sign leaf00333_log
#print axioms leaf00333_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
