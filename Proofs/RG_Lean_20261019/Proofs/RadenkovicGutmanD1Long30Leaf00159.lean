/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00159 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 14694165522632726735325495296000000000000 14255759389147067014282992061859657416704 1118523643886642101322225025024000000000000))
theorem leaf00159_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 14694165522632726735325495296000000000000 14255759389147067014282992061859657416704 1118523643886642101322225025024000000000000 raw00159=true := by decide +kernel
#print axioms leaf00159_raw
theorem leaf00159_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00159=true := by decide +kernel
#print axioms leaf00159_rectangular
def affine00159 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00159 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00159_transform : affine00159=(NestedInteger.clearedAll 3 raw00159 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00159_transform
theorem leaf00159_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00159=true := by decide +kernel
#print axioms leaf00159_sign
theorem leaf00159_log : RationalLog.accepts (2057193387/2147483648) (-46121675/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00159_log
def leaf00159 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6372578473/500000000000) (2057193387/2147483648) (-46121675/2147483648) 1 8 ![60,0,4] ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00159
theorem leaf00159_checked : FastNestedCellData.accepts 1 2 4 leaf00159=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6372578473/500000000000) (2057193387/2147483648) (-46121675/2147483648) 1 8 ![60,0,4] ![(109/32000),0,(1/2)] ![(3/32000),1,(1/2)] 14694165522632726735325495296000000000000 14255759389147067014282992061859657416704 1118523643886642101322225025024000000000000 raw00159 affine00159
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00159_raw leaf00159_rectangular
    leaf00159_transform leaf00159_sign leaf00159_log
#print axioms leaf00159_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
